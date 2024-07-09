theory SecurityAlg
  imports "../SecurityAlg" "HOL-Library.FSet" SepLogicExperimental
begin

section \<open> Location heaps \<close>

lemma dom_comp[simp]: \<open>dom (g \<circ>\<^sub>m f) = {a. \<exists>b. f a = Some b \<and> b \<in> dom g}\<close>
  by (force simp add: map_comp_def dom_def split: option.splits)

text \<open>
  For security applications, we need not just the data to be splittable, but also
  the \<^emph>\<open>locations\<close> of the heap. Being able to observe a location's existence can give
  security-relevant information, even without access to its data.
    Thus, we split the information that a location exists and a location's data into
  separate resources.
\<close>

typedef ('a,'b) locheap (infixr \<open>\<rightharpoonup>\<^sub>l\<close> 0) =
  \<open>{(L::'a set, h :: 'a \<rightharpoonup> 'b). dom h \<le> L}\<close>
  by blast

setup_lifting type_definition_locheap

setup \<open>Sign.mandatory_path "locheap"\<close>

lift_definition empty :: \<open>'a \<rightharpoonup>\<^sub>l 'b\<close> is \<open>({}, Map.empty)\<close>
  by force

lift_definition comp :: "('b \<rightharpoonup>\<^sub>l 'c) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'c)" (infixl "\<circ>\<^sub>l" 55) is
  \<open>\<lambda>(B ::'b set, g::'b \<rightharpoonup> 'c) (A::'a set, f::'a \<rightharpoonup> 'b). ({a. \<exists>b. f a = Some b \<and> b \<in> dom g}, g \<circ>\<^sub>m f)\<close>
  by (simp split: prod.splits)

lift_definition restrict :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)" (infixl \<open>|`\<^sub>l\<close> 110) is
  \<open>\<lambda>(A, m) B. (A \<inter> B, m |` B)\<close>
  by (auto split: prod.splits)

lift_definition dom :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set" is fst .
lift_definition precise_dom :: "('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a set" is \<open>dom \<circ> snd\<close> .

subsection \<open> (weak/permissive) leq \<close>

lift_definition less_eq :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> (infix \<open>\<subseteq>\<^sub>l\<close> 50) is
  \<open>\<lambda>(A,a) (B,b). A \<subseteq> B \<and> a \<subseteq>\<^sub>m b\<close> .

lemma less_eq_trans[trans]:
  \<open>a \<subseteq>\<^sub>l b \<Longrightarrow> b \<subseteq>\<^sub>l c \<Longrightarrow> a \<subseteq>\<^sub>l c\<close>
  by (transfer, force simp add: map_le_def dom_def split: prod.splits)

lemma less_eq_refl[iff]:
  \<open>a \<subseteq>\<^sub>l a\<close>
  by (transfer, simp split: prod.splits)

lemma less_eq_antisym:
  \<open>a \<subseteq>\<^sub>l b \<Longrightarrow> b \<subseteq>\<^sub>l a \<Longrightarrow> a = b\<close>
  by (transfer,
      clarsimp simp add: map_le_def dom_def fun_eq_iff split: prod.splits,
      metis not_Some_eq)

subsection \<open> strong leq \<close>

lift_definition strong_less_eq :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>l\<close> 50) is
  \<open>\<lambda>(A,a) (B,b). A = B \<and> a \<subseteq>\<^sub>m b\<close> .

lemma strong_less_eq_trans[trans]:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> b \<sqsubseteq>\<^sub>l c \<Longrightarrow> a \<sqsubseteq>\<^sub>l c\<close>
  by (transfer, force simp add: map_le_def dom_def split: prod.splits)

lemma strong_less_eq_refl[iff]:
  \<open>a \<sqsubseteq>\<^sub>l a\<close>
  by (transfer, simp split: prod.splits)

lemma strong_less_eq_antisym:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> b \<sqsubseteq>\<^sub>l a \<Longrightarrow> a = b\<close>
  by (transfer,
      clarsimp simp add: map_le_def dom_def fun_eq_iff split: prod.splits,
      metis not_Some_eq)

lemma strong_less_eq_impl_less_eq[dest]:
  \<open>a \<sqsubseteq>\<^sub>l b \<Longrightarrow> a \<subseteq>\<^sub>l b\<close>
  by (transfer, simp split: prod.splits)

subsection \<open> Locheap completion \<close>

lift_definition embed :: \<open>('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>\<lambda>h. (dom h, h)\<close>
  by simp

abbreviation completion :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>c\<close> 50) where
  \<open>lh \<sqsubseteq>\<^sub>c h \<equiv> lh \<sqsubseteq>\<^sub>l locheap.embed h\<close>

setup \<open>Sign.parent_path\<close>


instantiation locheap :: (type, type) plus
begin
lift_definition plus_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> 'a \<rightharpoonup>\<^sub>l 'b\<close> is
  \<open>\<lambda>(D1, m1) (D2, m2). (D1 \<union> D2, m1 ++ m2)\<close>
  by force
instance by standard
end

instantiation locheap :: (type, perm_alg) perm_alg
begin

lift_definition disjoint_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> bool\<close> is
  \<open>\<lambda>(D1, m1) (D2, m2). D1 \<inter> D2 = {}\<close> .

instance
  apply standard
       apply (transfer, force)
      apply (transfer, simp split: prod.splits)
      apply (metis map_add_comm order_bot_class.bot.extremum_uniqueI semilattice_inf_class.inf_mono sup.commute)
     apply (transfer, force)
    apply (transfer, fastforce)
   apply (transfer, fastforce)
  apply (transfer, clarsimp split: prod.splits)
  apply (metis Un_Int_assoc_eq Un_Int_eq(1,3) empty_iff map_add_subsumed2 map_le_def sup_bot_left)
  done

end

instantiation locheap :: (type, perm_alg) multiunit_sep_alg
begin
lift_definition unitof_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b) \<Rightarrow> ('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>\<lambda>_. ({}, Map.empty)\<close>
  by (simp split: prod.splits)
instance by standard (transfer, force)+
end

instantiation locheap :: (type, perm_alg) sep_alg
begin

lift_definition zero_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>({}, Map.empty)\<close>
  by (simp split: prod.splits)

lift_definition bot_locheap :: \<open>('a \<rightharpoonup>\<^sub>l 'b)\<close> is
  \<open>({}, Map.empty)\<close>
  by (simp split: prod.splits)

instance
  by standard
    (transfer, force)+

end

section \<open> Set reasoning \<close>

lemma \<open>r x y \<or> r y x \<Longrightarrow> tranclp (symclp r) x x\<close>
  by (metis symclpI1 symclpI2 tranclp.simps)

abbreviation inf_Times :: \<open>('a::inf) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<sqinter>\<times>\<close> 90) where
  \<open>A \<times>\<sqinter>\<times> B \<equiv> case_prod (\<sqinter>) ` (A \<times> B)\<close>

abbreviation sup_Times :: \<open>('a::sup) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<squnion>\<times>\<close> 85) where
  \<open>A \<times>\<squnion>\<times> B \<equiv> case_prod (\<squnion>) ` (A \<times> B)\<close>

abbreviation implies_Times :: \<open>('a::boolean_algebra) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> (infixr \<open>\<times>\<leadsto>\<times>\<close> 80) where
  \<open>A \<times>\<leadsto>\<times> B \<equiv> case_prod (\<leadsto>) ` (A \<times> B)\<close>

definition
  \<open>equiv_rel_to_equiv_classes r \<equiv>
    {A. (\<exists>x y. (x,y) \<in> r \<and> x \<in> A \<and> y \<in> A) \<and>
          (\<forall>x y. x \<in> A \<longrightarrow> (x,y) \<in> r \<longrightarrow> y \<in> A)}\<close>

lemma Un_contains_eq:
  fixes A :: \<open>'a set\<close>
  shows \<open>A \<in> \<AA> \<Longrightarrow> \<Union> ((\<union>) A ` \<AA>) = \<Union> \<AA>\<close>
  by (drule mk_disjoint_insert, clarsimp)

(* proof from Liam O'Connor *)
lemma Sup_contains_eq:
  fixes a :: \<open>'a :: complete_lattice\<close>
  assumes \<open>a \<in> A\<close>
  shows \<open>\<Squnion> ((\<squnion>) a ` A) = \<Squnion> A\<close>
proof (rule antisym)
  show \<open>\<Squnion> ((\<squnion>) a ` A) \<le> \<Squnion> A\<close> by (simp add: SUP_least Sup_upper assms)
next
  show \<open>\<Squnion> A \<le> \<Squnion> ((\<squnion>) a ` A)\<close> by (metis Sup_least Sup_upper image_eqI le_sup_iff)
qed

lemma un_Un_eq_Un_un_every:
  fixes a :: \<open>'a set\<close>
  shows \<open>\<AA> \<noteq> {} \<Longrightarrow> A \<union> \<Union> \<AA> = \<Union> ((\<union>) A ` \<AA>)\<close>
  by blast

lemma sup_Sup_eq_Sup_sup_every:
  fixes a :: \<open>'a :: complete_lattice\<close>
  assumes \<open>A \<noteq> {}\<close>
  shows \<open>a \<squnion> \<Squnion> A = \<Squnion> ((\<squnion>) a ` A)\<close>
  apply (intro order.antisym le_supI)
    apply (meson assms SUP_upper2 ex_in_conv sup_ge1)
   apply (metis Sup_mono imageI sup.cobounded2)
  apply (metis SUP_least Sup_upper order_refl sup.mono)
  done

lemma supcl_allsup_export:
  fixes a :: \<open>'a::complete_lattice\<close>
  shows \<open>supcl ((\<squnion>) a ` B) = (\<squnion>) a ` supcl B\<close>
  apply (rule antisym)
  subgoal
    apply (clarsimp simp add: supcl_def image_def subset_iff
        Ball_def[symmetric] Bex_def)
    apply (drule bchoice)
    apply (clarsimp simp add: Ball_def subset_iff[symmetric])
    apply (rule_tac x=\<open>\<Squnion>(f ` A')\<close> in exI)
    apply (rule conjI)
     apply blast
    apply (simp add: sup_Sup_eq_Sup_sup_every)
    apply (rule arg_cong[of _ _ Sup])
    apply force
    done
  apply (clarsimp simp add: supcl_def image_def subset_iff
      Ball_def Bex_def)
  apply (rule_tac x=\<open>(\<squnion>) a ` A'\<close> in exI)
  apply (meson image_iff image_is_empty sup_Sup_eq_Sup_sup_every)
  done


lemma mono_comp:
  \<open>mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f \<circ> g)\<close>
  by (simp add: monotone_on_o)

definition
  \<open>set_plus A \<equiv>
    ((`) (case_prod (+)) \<circ> Set.filter (case_prod (##)) \<circ> (\<times>) A)\<close>

lemma
  \<open>{a + b |a b. a \<in> A \<and> b \<in> B \<and> a ## b} = set_plus A B\<close>
  unfolding set_plus_def
  by (simp add: set_eq_iff image_def Set.filter_def, blast)

lemma onesided_plus_mono:
  \<open>mono (set_plus B)\<close>
  by (force simp add: set_plus_def mono_def image_def Set.filter_def split: prod.splits)

lemma
  fixes x :: \<open>'a :: complete_lattice\<close>
  shows \<open>
    Lt = {(x::'a,y). x < y} \<Longrightarrow>
    f (g x) = x \<Longrightarrow>
    \<forall>A. \<Squnion>((f \<circ> g) ` A) = (f \<circ> g) (\<Squnion>A) \<Longrightarrow>
    \<forall>A. \<Squnion>((f) ` A) = (f) (\<Squnion>A) \<Longrightarrow>
    \<forall>A. \<Squnion>((g) ` A) = (g) (\<Squnion>A) \<Longrightarrow>
    mono f \<Longrightarrow>
    mono g \<Longrightarrow>
    f x = x\<close>
  oops

lemma
  fixes A B :: \<open>('a::canonically_ordered_monoid_add) set\<close>
  assumes
    \<open>A \<noteq> {}\<close>
    \<open>B \<noteq> {}\<close>
    \<open>AB = {a + b|a b. a \<in> A \<and> b \<in> B}\<close>
  shows
    \<open>A \<le>\<^sub>P AB\<close>
    \<open>B \<le>\<^sub>P AB\<close>
  using assms
  by (force simp add: leq_plotkin_def' le_iff_add add.commute)+

lemma canonically_ordered_set_add_trans_plotkin:
  fixes X :: \<open>('a::canonically_ordered_monoid_add) set\<close>
  assumes
    \<open>A \<noteq> {}\<close>
    \<open>B \<noteq> {}\<close>
    \<open>{x + a + b|x a b. x \<in> X \<and> a \<in> A \<and> b \<in> B} = X\<close>
  shows
    \<open>{x + a|x a. x \<in> X \<and> a \<in> A} =\<^sub>P X\<close>
proof -
  have \<open>X \<le>\<^sub>P {x + a|x a. x \<in> X \<and> a \<in> A}\<close>
    using assms
    by (force simp add: leq_plotkin_def' le_iff_add)
  moreover have \<open>... \<le>\<^sub>P {x + a + b|x a b. x \<in> X \<and> a \<in> A \<and> b \<in> B}\<close>
    using assms
    by (clarsimp simp add: leq_plotkin_def' le_iff_add, blast)
  ultimately show ?thesis
    using assms eq_plotkin_def
    by force
qed

(*
lemma
  fixes A B :: \<open>('a::canonically_ordered_monoid_add) set\<close>
  shows \<open>A =\<^sub>P B \<Longrightarrow> A = B\<close>
  nitpick
  oops

lemma perm_alg_set_add_trans_plotkin:
  fixes A B :: \<open>('a::{perm_alg,order}) set\<close>
  assumes \<open>((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) = (\<preceq>)\<close>
  shows \<open>A =\<^sub>S B \<Longrightarrow> A = B\<close>
  nitpick
  oops
*)


lemma
  fixes X :: \<open>('a::{plus,disjoint}) set\<close>
  (* partial commutative monoid *)
  assumes partial_add_assoc: \<open>\<And>a b c::'a. a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>\<And>a b::'a. a ## b \<Longrightarrow> a + b = b + a\<close>
  assumes disjoint_sym: \<open>\<And>a b::'a. a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>\<And>a b c::'a. b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>\<And>a b c::'a. b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b ## a + c\<close>
  (* separation laws *)
  assumes positivity:
    \<open>\<And>a b c1 c2::'a. a ## c1 \<Longrightarrow> a + c1 = b \<Longrightarrow> b ## c2 \<Longrightarrow> b + c2 = a \<Longrightarrow> a = b\<close>
  assumes
    \<open>\<And>A. ff A = \<Squnion>((\<lambda>a. {a + b |b. b \<in> F \<and> a ## b}) ` A)\<close>
    \<open>\<And>A. gg A = \<Squnion>((\<lambda>a. {a + b |b. b \<in> G \<and> a ## b}) ` A)\<close>
    \<open>ffgg = ff \<circ> gg\<close>
    \<open>F = {x}\<close>
    \<open>G = {y}\<close>
  shows
  \<open>(d :: 'a \<times> _ \<Rightarrow> _) = case_prod (##) \<Longrightarrow>
    (p :: 'a \<times> _ \<Rightarrow> _) = case_prod (+) \<Longrightarrow>
    ffgg X = X \<Longrightarrow> ff X = X\<close>
  oops

lemma all_iff_conv:
  fixes p q :: \<open>_ \<Rightarrow> bool\<close>
  shows \<open>(\<forall>x. p x = q x) \<longleftrightarrow> p \<le> q \<and> q \<le> p\<close>
  by force

lemma set_eq_choice2_iff:
  \<open>A = {f x y|x y. P x y} \<longleftrightarrow>
    (\<exists>g1 g2. \<forall>a\<in>A. a = f (g1 a) (g2 a) \<and> P (g1 a) (g2 a)) \<and>
    (\<forall>x y. P x y \<longrightarrow> (\<exists>a\<in>A. a = f x y))\<close>
  by (simp add: set_eq_iff all_iff_conv le_fun_def choice_iff', blast)

lemma set_eq_choice3_iff:
  \<open>A = {f x y z|x y z. P x y z} \<longleftrightarrow>
    (\<exists>g1 g2 g3. \<forall>a\<in>A. a = f (g1 a) (g2 a) (g3 a) \<and> P (g1 a) (g2 a) (g3 a)) \<and>
    (\<forall>x y z. P x y z \<longrightarrow> (\<exists>a\<in>A. a = f x y z))\<close>
  by (simp add: set_eq_iff all_iff_conv le_fun_def choice_iff', fast)

lemma
  fixes A C1 C2 :: \<open>('a::multiunit_sep_alg) set\<close>
  assumes
    \<open>dd A C1\<close>
    \<open>dd {a + b |a b. a \<in> A \<and> b \<in> C1 \<and> a ## b} C2\<close>
    \<open>{(a + x) + y|a x y.
                  a \<in> A \<and> x \<in> C1 \<and> y \<in> C2 \<and>
                  a ## x \<and> a + x ## y } = A\<close>
  shows
    \<open>{ a + x |a x. a \<in> A \<and> x \<in> C1 \<and> a ## x } = A\<close>
proof -

  obtain fa fc1 fc2 where triple_choice:
    \<open>\<forall>a\<in>A. a = fa a + fc1 a + fc2 a\<close>
    \<open>\<forall>a\<in>A. fa a \<in> A\<close>
    \<open>\<forall>a\<in>A. fc1 a \<in> C1\<close>
    \<open>\<forall>a\<in>A. fc2 a \<in> C2\<close>
    \<open>\<forall>a\<in>A. fa a ## fc1 a\<close>
    \<open>\<forall>a\<in>A. fa a + fc1 a ## fc2 a\<close>
    \<open>\<forall>a\<in>A. \<forall>c1\<in>C1. \<forall>c2\<in>C2.
        a ## c1 \<longrightarrow> a + c1 ## c2 \<longrightarrow> a + c1 + c2 \<in> A\<close>
    using assms(3)
    by (simp add: trans[OF eq_commute set_eq_choice3_iff], fast)

  have \<open>\<forall>a\<in>A. fa a \<preceq> a\<close>
    using triple_choice
    sorry
  (* oops
    by (metis less_eq_sepadd_def) *)

  show ?thesis
    using assms(3)
    apply (simp add: trans[OF eq_commute set_eq_choice2_iff])
    apply (rule conjI)
     prefer 2
     apply clarsimp
     apply (case_tac \<open>\<exists>a'. a' \<preceq> a \<and> a' \<in> A \<and> fa a' = a'\<close>)
      apply clarsimp
      apply (subgoal_tac \<open>\<exists>x'\<in>C1. \<exists>y'\<in>C2.
                            a' ## x' \<and> a' + x' ## y' \<and> a' + x' + y' = a'\<close>)
       prefer 2
       apply (metis triple_choice(1,3-6))
      apply clarsimp
      apply (drule unit_sub_closure2'[rotated 2], blast, blast)
      apply simp
      apply (simp add: less_eq_sepadd_def)
      apply (erule disjE)
       apply simp
    oops


definition
  \<open>seple_rel = {(a,b). a \<noteq> b \<and> (\<exists>c::'a::perm_alg. a ## c \<and> a + c = b)}\<close>

(*

lemma seple_rel_prec:
  fixes x :: \<open>'a :: perm_alg\<close>
  shows \<open>(x,y) \<in> seple_rel\<^sup>+ \<Longrightarrow> x \<prec> y\<close>
  apply (induct rule: trancl.induct)
   apply (clarsimp simp add: seple_rel_def less_sepadd_def')+
  apply (metis perm_alg_class.positivity trans_helper)
  done

lemma
  fixes x :: \<open>'a :: perm_alg\<close>
  shows \<open>(x,y) \<in> seple_rel\<^sup>+ \<Longrightarrow> x = y \<Longrightarrow> False\<close>
  apply (induct rule: trancl.induct)
   apply (simp add: seple_rel_def)
  apply (drule seple_rel_prec)
  apply (clarsimp simp add: seple_rel_def)
  apply (simp add: partial_le_plus resource_order.leD)
  done

typedef inat = \<open>UNIV :: nat set\<close>
  by blast
setup_lifting type_definition_inat
*)

lemma fperm_exI:
  fixes x :: \<open>'a :: {linordered_semiring,zero_less_one}\<close>
  shows \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> P x \<Longrightarrow> \<exists>x::'a fperm. P (fperm_val x)\<close>
  by (metis FPerm_inverse_iff)

lemma
  \<open>(UNIV :: rat fperm set) + {x. x < 1} = UNIV\<close>
  apply (clarsimp simp add: plus_set_def set_eq_iff)
  apply (simp add: plus_fperm_def less_fperm_def disjoint_fperm_def)
  apply (subst eq_FPerm_iff)
    apply (force simp add: fperm_val_add_gt0)
   apply force
  apply (rule_tac x=\<open>fperm_val x / 2\<close> in fperm_exI)
    apply (simp add: fperm_val_conditions; fail)
   apply (metis fperm_val_conditions(2) half_fperm.rep_eq)
  apply (rule_tac x=\<open>fperm_val x / 2\<close> in fperm_exI)
    apply (simp add: fperm_val_conditions; fail)
   apply (metis fperm_val_conditions(2) half_fperm.rep_eq)
  apply (simp add: fperm_val_conditions)
  apply (metis fperm_val_conditions(2) less_add_same_cancel1 mult_1
      one_add_one one_fperm.rep_eq order_le_less pos_add_strict zero_less_one)
  done

lemma
  fixes X :: \<open>rat fperm set\<close>
  shows
    \<open>(\<forall>y. \<exists>x\<in>X + Y. x < y) \<Longrightarrow>
      (\<forall>y. \<exists>x\<in>X. x < y)\<close>
  apply (clarsimp simp add: Bex_def plus_set_def)
  apply (drule_tac x=y in spec)
  apply clarsimp
  apply (rule_tac x=a in exI)
  apply (simp add: disjoint_fperm_iff less_fperm_def plus_fperm.rep_eq)
  apply (meson fperm_val_conditions(1) less_add_same_cancel1 order.strict_trans)
  done

lemma
  \<open>(\<forall>y. \<exists>x\<in>X. x < y) \<Longrightarrow> (UNIV :: rat fperm set) + X = UNIV\<close>
  apply (clarsimp simp add: plus_set_def set_eq_iff)
  apply (simp add: plus_fperm_def less_fperm_def disjoint_fperm_def)
  apply (subst eq_FPerm_iff)
    apply (force simp add: fperm_val_add_gt0)
   apply force
  apply (rename_tac y)
  apply (drule_tac x=y in spec)
  apply clarsimp
  apply (rule_tac x=\<open>FPerm (fperm_val y - fperm_val x)\<close> in exI)
  apply (rule_tac x=x in exI)
  apply (subst FPerm_inverse_iff)
    apply (metis diff_gt_0_iff_gt fperm_val_conditions
      less_eq_rat_def less_fperm_def add_diff_inverse not_less_iff_gr_or_eq
      pos_add_strict)
  apply (subst FPerm_inverse_iff)
    apply (metis diff_gt_0_iff_gt fperm_val_conditions
      less_eq_rat_def less_fperm_def add_diff_inverse not_less_iff_gr_or_eq
      pos_add_strict)
  apply (rule conjI)
   apply (simp add: fperm_val_conditions(2); fail)
  apply (simp add: fperm_val_conditions(2); fail)
  done

lemma
  \<open>P = {(x,y). 0 < (x::rat zoint) \<and> 0 < (y::rat zoint)} \<Longrightarrow>
    P = {(x,0)|x. 0 < x} + {(0,y)|y. 0 < y}\<close>
  by (clarsimp simp add: plus_set_def set_eq_iff)

lemma
  \<open>P = {(x,y). 0 < (x::rat zoint) \<and> 0 < (y::rat zoint)} \<Longrightarrow>
    P + {(x,0)|x. 0 < x} = P\<close>
  apply (clarsimp simp add: plus_set_def set_eq_iff)
apply (simp add: disjoint_zoint_def)
  apply (intro iffI; elim exE conjE)
   apply (simp add: zoint_val_inject_rev plus_zoint.rep_eq
      less_zoint_def; fail)
   apply (simp add: zoint_val_inject_rev plus_zoint.rep_eq less_zoint_def)
  apply (rule_tac x=\<open>ZOInt (zoint_val a / 2)\<close> in exI)
  apply (rule_tac x=\<open>ZOInt (zoint_val a / 2)\<close> in exI)
  apply simp
  apply (subst ZOInt_inverse_iff,
      metis half_zoint.rep_eq zoint_val_conditions)+
  apply (simp add: zoint_val_conditions)
  done

definition \<open>sepequivs x \<equiv> insert x {x+u | u. x ## u \<and> (\<exists>a. a+u = a)}\<close>

lemma sepequiv_closed_iff:
  \<open>\<Union>(sepequivs ` A) = A \<longleftrightarrow> (\<forall>x\<in>A. \<forall>u. (\<exists>a. a+u = a) \<longrightarrow> x ## u \<longrightarrow> x+u \<in> A)\<close>
  by (force simp add: sepequivs_def set_eq_iff)


context perm_alg
begin

lemma unit_disjoint_inherit:
  shows \<open>a ## u \<Longrightarrow> a + u = a \<Longrightarrow> a ## x \<Longrightarrow> u ## x\<close>
  by (metis disjoint_add_leftR)

end

(*
  a j + (c1 + c2) = a z
and
  a z + (c1 + c2') = a i
means that
  a j ## c1 + c2'
*)

lemma sepadd_cancel_then_inj:
  fixes x :: \<open>'a :: cancel_perm_alg\<close>
  assumes \<open>\<forall>a\<in>A. x ## a\<close>
  shows \<open>inj_on ((+) x) A\<close>
  using assms
  by (simp add: inj_on_def)


theorem Schroeder_Bernstein_exact:
  fixes f :: \<open>'a \<Rightarrow> 'b\<close>
    and g :: \<open>'b \<Rightarrow> 'a\<close>
    and A :: \<open>'a set\<close>
    and B :: \<open>'b set\<close>
  defines \<open>X \<equiv> lfp (\<lambda>X. A - (g ` (B - (f ` X))))\<close>
  defines \<open>g' \<equiv> the_inv_into (B - (f ` X)) g\<close>
  defines \<open>h \<equiv> (\<lambda>z. if z \<in> X then f z else g' z)\<close>
  assumes inj1: "inj_on f A" and sub1: "f ` A \<subseteq> B"
    and inj2: "inj_on g B" and sub2: "g ` B \<subseteq> A"
  shows "bij_betw h A B"
proof (rule bij_betw_imageI)
  have X: "X = A - (g ` (B - (f ` X)))"
    unfolding X_def by (rule lfp_unfold) (blast intro: monoI)
  then have X_compl: "A - X = g ` (B - (f ` X))"
    using sub2 by blast

  from inj2 have inj2': "inj_on g (B - (f ` X))"
    by (rule inj_on_subset) auto
  with X_compl have *: "g' ` (A - X) = B - (f ` X)"
    by (simp add: g'_def)

  from X have X_sub: "X \<subseteq> A" by auto
  from X sub1 have fX_sub: "f ` X \<subseteq> B" by auto

  show "h ` A = B"
  proof -
    from X_sub have "h ` A = h ` (X \<union> (A - X))" by auto
    also have "\<dots> = h ` X \<union> h ` (A - X)" by (simp only: image_Un)
    also have "h ` X = f ` X" using h_def by auto
    also from * have "h ` (A - X) = B - (f ` X)" using h_def by auto
    also from fX_sub have "f ` X \<union> (B - f ` X) = B" by blast
    finally show ?thesis .
  qed
  show "inj_on h A"
  proof -
    from inj1 X_sub have on_X: "inj_on f X"
      by (rule subset_inj_on)

    have on_X_compl: "inj_on g' (A - X)"
      unfolding g'_def X_compl
      by (rule inj_on_the_inv_into) (rule inj2')

    have impossible: False if eq: "f a = g' b" and a: "a \<in> X" and b: "b \<in> A - X" for a b
    proof -
      from a have fa: "f a \<in> f ` X" by (rule imageI)
      from b have "g' b \<in> g' ` (A - X)" by (rule imageI)
      with * have "g' b \<in> - (f ` X)" by simp
      with eq fa show False by simp
    qed

    show ?thesis
    proof (rule inj_onI)
      fix a b
      assume h: "h a = h b"
      assume "a \<in> A" and "b \<in> A"
      then consider "a \<in> X" "b \<in> X" | "a \<in> A - X" "b \<in> A - X"
        | "a \<in> X" "b \<in> A - X" | "a \<in> A - X" "b \<in> X"
        by blast
      then show "a = b"
      proof cases
        case 1
        with h on_X show ?thesis using h_def by (simp add: inj_on_eq_iff)
      next
        case 2
        with h on_X_compl show ?thesis using h_def by (simp add: inj_on_eq_iff)
      next
        case 3
        with h impossible [of a b] have False using h_def by simp
        then show ?thesis ..
      next
        case 4
        with h impossible [of b a] have False using h_def by simp
        then show ?thesis ..
      qed
    qed
  qed
qed

lemma subset_subset_bij_betw_then_bij_betw:
  fixes f g A B A' B'
  defines \<open>X \<equiv> lfp (\<lambda>X. A - (g ` (B - (f ` X))))\<close>
  defines \<open>g' \<equiv> the_inv_into (B - (f ` X)) g\<close>
  defines \<open>h \<equiv> (\<lambda>z. if z \<in> X then f z else g' z)\<close>
  assumes
    \<open>bij_betw g B A'\<close>
    \<open>bij_betw f A B'\<close>
    \<open>A' \<subseteq> A\<close>
    \<open>B' \<subseteq> B\<close>
  shows
    \<open>bij_betw h A B\<close>
  unfolding h_def g'_def X_def
  using assms
  by (intro Schroeder_Bernstein_exact) (metis bij_betw_def)+

lemma inv_into_inv_into_eq:
  fixes f :: \<open>'a \<Rightarrow> 'b\<close>
    and A :: \<open>'a set\<close>
    and B :: \<open>'b set\<close>
  assumes
    \<open>x \<in> A\<close>
    \<open>bij_betw f A B\<close>
  shows \<open>the_inv_into B (the_inv_into A f) x = f x\<close>
  using assms
  by (metis bij_betw_apply bij_betw_def inj_on_the_inv_into the_inv_into_f_eq)

lemma inv_sepadd_cancel:
  fixes x :: \<open>'a::cancel_perm_alg\<close>
  shows \<open>a \<in> A \<Longrightarrow> \<forall>a\<in>A. x ## a \<Longrightarrow> the_inv_into A ((+) x) (x + a) = a\<close>
  by (force intro: the_inv_into_f_f simp add: inj_on_def)


lemma test1:
  fixes A1 A2 :: \<open>('a::cancel_perm_alg) set\<close>
  assumes
    \<open>\<forall>a\<in>A1'. a ## c12\<close>
    \<open>(+) c12 ` A1' = A2\<close>
    \<open>\<forall>a\<in>A2'. a ## c21\<close>
    \<open>(+) c21 ` A2' = A1\<close>
    \<open>A1' \<subseteq> A1\<close>
    \<open>A2' \<subseteq> A2\<close>
  shows
    \<open>\<exists>Z. A1 + Z = A2\<close>
proof -
  have \<open>bij_betw ((+) c12) A1' A2\<close>
    using assms(1-2)
    by (simp add: bij_betw_def inj_on_def)
  then have L1: \<open>bij_betw (the_inv_into A1' ((+) c12)) A2 A1'\<close>
    by (simp add: bij_betw_the_inv_into)

  have \<open>bij_betw ((+) c21) A2' A1\<close>
    using assms(3-4)
    by (simp add: bij_betw_def inj_on_def)
  then have L2: \<open>bij_betw (the_inv_into A2' ((+) c21)) A1 A2'\<close>
    by (simp add: bij_betw_the_inv_into)
  let ?X = \<open>lfp (\<lambda>X. A1 - the_inv_into A1' ((+) c12) ` (A2 - the_inv_into A2' ((+) c21) ` X))\<close>
  let ?g' = \<open>the_inv_into
              (A2 - the_inv_into A2' ((+) c21) ` ?X)
              (the_inv_into A1' ((+) c12))\<close>
  have \<open>bij_betw (\<lambda>z. if z \<in> ?X then the_inv_into A2' ((+) c21) z else ?g' z) A1 A2\<close>
    using subset_subset_bij_betw_then_bij_betw[OF L1 L2 assms(5-6)] .
  show ?thesis
    oops


lemma test2:
  fixes A :: \<open>('a::perm_alg) set\<close>
    and a :: \<open>nat \<Rightarrow> 'a\<close>
  assumes
    \<open>\<forall>i. \<forall>j<i. a i \<noteq> a j\<close>
    and
    \<open>c1 ## c2\<close>
    \<open>\<forall>i. a i ## c1 + c2\<close>
    \<open>\<forall>i. a i + (c1 + c2) = a (Suc i)\<close>
    and
    \<open>c1 ## c2'\<close>
    \<open>a 0 ## c1 + c2'\<close>
    \<open>\<exists>j>0. a j + (c1 + c2') = a 0\<close>
    \<open>\<forall>i>0. \<not> a i ## c1 + c2'\<close>
  shows
    \<open>False\<close>
  oops


lemma set_positivity:
  fixes A :: \<open>('a::perm_alg) set\<close>
  shows \<open>A + (C1 + C2) = A \<Longrightarrow> A + C1 = A\<close>
  apply -
  apply (clarsimp simp add: set_eq_iff)
  apply (case_tac \<open>\<exists>u\<in>C1 + C2. x ## u \<and> x + u = x\<close>)
    (* case 1 *)
   apply clarsimp
   apply (subgoal_tac \<open>\<exists>u1 u2. u = u1 + u2 \<and> u1 \<in> C1 \<and> u2 \<in> C2 \<and> u1 ## u2\<close>)
    prefer 2
    apply (simp add: plus_set_def; fail)
   apply clarsimp
   apply (subgoal_tac \<open>x + u1 = x\<close>)
    prefer 2
    apply (metis disjoint_add_rightL disjoint_add_swap_rl unit_sub_closure2)
   apply (clarsimp simp add: plus_set_def)
   apply (rule iffI)
    apply (metis disjoint_add_leftR disjoint_add_rightR disjoint_add_swap_lr partial_add_assoc3)
   apply (metis disjoint_add_rightL)
    (* case 2 *)
  apply clarsimp
  apply (subgoal_tac \<open>\<forall>c\<in>C1 + C2. x ## c \<longrightarrow> x \<prec> x + c\<close>)
   prefer 2
   apply (simp add: less_sepadd_def', metis)
  apply (rule iffI)
    (* case 2\<rightarrow> *)
  subgoal sorry
    (* case 2\<leftarrow> *)
  apply (subgoal_tac \<open>\<exists>a'\<in>A. \<exists>c'\<in>C1 + C2. a' ## c' \<and> a' + c' = x\<close>)
   prefer 2
   apply (clarsimp simp add: plus_set_def[of A])
   apply metis
  apply clarsimp
  oops

(*
lemma bij_betw_empty_eq[simp]:
  \<open>bij_betw f {} X \<longleftrightarrow> X = {}\<close>
  using bij_betw_def by auto

lemma plus_set_empty_eq[simp]:
  \<open>X + {} = {}\<close>
  \<open>{} + Y = {}\<close>
  by (simp add: plus_set_def)+

lemma range_top_split:
  fixes k :: nat
  shows \<open>{0..k} = insert k {0..<k}\<close>
  by (metis atLeast0LessThan atLeastLessThanSuc_atLeastAtMost lessThan_Suc)

lemma bij_betw_insertL:
  assumes \<open>a \<notin> A\<close>
  shows \<open>bij_betw f (insert a A) B \<longleftrightarrow> (f a \<in> B \<and> bij_betw f A (B - {f a}))\<close>
  apply (rule iffI)
   apply (metis (no_types, lifting) Diff_insert_absorb assms bij_betw_def image_insert inj_on_insert
      insertCI insert_Diff_single)
  apply (metis Diff_iff bij_betw_combine_insert insertCI insert_Diff)
  done

lemma un_eq_insert_avoiding_iff:
  \<open>x \<notin> B \<Longrightarrow> A \<union> B = insert x B \<longleftrightarrow> (x \<in> A \<and> A \<subseteq> insert x B)\<close>
  by blast
*)

lemma insert_plus_set_eqL:
  \<open>insert a A + B = {a+b|b. b\<in>B \<and> a ## b} \<union> (A + B)\<close>
  by (simp add: plus_set_def conj_disj_distribL conj_disj_distribR ex_disj_distrib Collect_disj_eq)

lemma insert_plus_set_eqR:
  \<open>A + insert b B = {a+b|a. a\<in>A \<and> a ## b} \<union> (A + B)\<close>
  by (simp add: plus_set_def conj_disj_distribL conj_disj_distribR ex_disj_distrib Collect_disj_eq)

lemma plus_set_singleton_left_leq:
  \<open>ab \<in> {a} + B \<Longrightarrow> a \<preceq> ab\<close>
  by (force simp add: less_eq_sepadd_def plus_set_def)

lemma plus_set_singleton_left_no_unit_less:
  \<open>ab \<in> {a} + B \<Longrightarrow> \<forall>b\<in>B. a ## b \<longrightarrow> a + b \<noteq> a \<Longrightarrow> a \<prec> ab\<close>
  by (force simp add: Ball_def less_sepadd_def' plus_set_def)

lemma plus_set_singleton_left_self_mem_then_some_unit:
  \<open>a \<in> {a} + B \<Longrightarrow> \<exists>b\<in>B. a ## b \<and> a + b = a\<close>
  by (force simp add: Ball_def less_sepadd_def' plus_set_def)


lemma singleton_plus_set_eq:
  \<open>{a} + B = {a+b|b. b\<in>B \<and> a ## b}\<close>
  by (simp add: plus_set_def conj_disj_distribL conj_disj_distribR ex_disj_distrib Collect_disj_eq)

lemma plus_set_eq_plus_left_members:
  \<open>A + B = (\<Union>a\<in>A. {a} + B)\<close>
  by (force simp add: Ball_def less_eq_sepadd_def plus_set_def)

lemma minset_sepadd_unit_set_contains_unit:
  fixes A :: \<open>('a::perm_alg) set\<close>
  assumes Cpunit: \<open>A + C = A\<close>
    and minAs:\<open>\<forall>a\<in>A. \<exists>la\<in>A. la \<preceq> a \<and> (\<forall>a'\<in>A. \<not> a' \<prec> la)\<close>
  shows \<open>\<forall>a\<in>A. \<exists>c\<in>C. a ## c \<and> a + c = a\<close>
proof clarsimp
  fix a
  assume a_mem_A: \<open>a \<in> A\<close>

  define Crel :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
    \<open>Crel = (\<lambda>x y. y \<in> {x} + C \<and> x \<noteq> y)\<close>

  have Crel_less:
    \<open>\<And>x y. Crel x y \<Longrightarrow> x \<prec> y\<close>
    unfolding Crel_def
    by (metis plus_set_singleton_left_leq resource_ordering.not_eq_order_implies_strict)
  
  have Crel_transcl_less:
    \<open>\<And>x y. Crel\<^sup>+\<^sup>+ x y \<Longrightarrow> x \<prec> y\<close>
    by (erule tranclp_induct, metis Crel_less, metis Crel_less resource_preordering.strict_trans)

  have assum1': \<open>(\<Union>a\<in>A. {a} + C) = A\<close>
    using assms
    by (metis plus_set_eq_plus_left_members)

  have downwards_not_selfC:
    \<open>\<And>x y . x \<notin> {x} + C \<Longrightarrow> Crel y x \<Longrightarrow> y \<notin> {y} + C\<close>
    unfolding Crel_def
    apply (clarsimp simp add: singleton_plus_set_eq)
    apply (metis disjoint_add_left_commute2 partial_add_right_commute unit_disjoint_inherit)
    done

  let ?minimalA = \<open>{a\<in>A. \<forall>x\<in>A. \<not> x \<prec> a}\<close>

  let ?minimalCrelA = \<open>{a\<in>A. \<forall>x\<in>A. x = a \<or> \<not> Crel x a}\<close>

  have minA_subseteq_minCrelA: \<open>?minimalA \<subseteq> ?minimalCrelA\<close>
    using Crel_def plus_set_singleton_left_leq Crel_less
    by blast

  have \<open>\<And>x. x \<in> A \<Longrightarrow> \<exists>w\<in>?minimalCrelA. w \<preceq> x\<close>
    using minA_subseteq_minCrelA assms(2)
    by (clarsimp simp add: Ball_def Bex_def) fast
  then obtain mina where mina_conds: \<open>mina \<in> ?minimalCrelA\<close> \<open>mina \<preceq> a\<close>
    by (meson a_mem_A)

  {
    fix x
    assume assmsB: \<open>x \<in> ?minimalCrelA\<close>

    have \<open>\<forall>w\<in>A. \<not> Crel w x\<close>
      using assmsB Crel_less by force
    then have \<open>x \<in> {x} + C\<close>
      using assms(1) assmsB
      unfolding Crel_def
      by (clarsimp, metis (no_types, lifting) UN_iff plus_set_eq_plus_left_members)
  } note H2 = this
  
  show \<open>\<exists>c\<in>C. a ## c \<and> a + c = a\<close>
    using H2[OF mina_conds(1)] mina_conds(2)
    apply (metis disjoint_sym partial_add_commute plus_set_singleton_left_self_mem_then_some_unit
        sepadd_punit_of_unit_res_mono')
    done
qed

lemma test_unit_set_contains_unit:
  fixes A :: \<open>('a::perm_alg) set\<close>
  assumes Cpunit: \<open>A + C = A\<close>
    and C_reduced: \<open>\<forall>c\<in>C. \<exists>a\<in>A. a ## c\<close>
    and never_punit_C: \<open>\<forall>a\<in>A. a \<notin> {a} + C\<close>
  shows \<open>\<forall>C1 C2. C = C1 + C2 \<longrightarrow> (\<forall>c\<in>C1. \<exists>a\<in>A. a ## c) \<longrightarrow> (A + C1 = A)\<close>
proof clarsimp
  fix C1 C2
  assume assmsP1:
    \<open>C = C1 + C2\<close>
    \<open>\<forall>c\<in>C1. \<exists>a\<in>A. a ## c\<close>

  define Crel :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
    \<open>Crel = (\<lambda>x y. y \<in> {x} + C \<and> x \<noteq> y)\<close>

  have Crel_less:
    \<open>\<And>x y. Crel x y \<Longrightarrow> x \<prec> y\<close>
    unfolding Crel_def
    by (metis plus_set_singleton_left_leq resource_ordering.not_eq_order_implies_strict)
  
  have Crel_transcl_less:
    \<open>\<And>x y. Crel\<^sup>+\<^sup>+ x y \<Longrightarrow> x \<prec> y\<close>
    by (erule tranclp_induct, metis Crel_less, metis Crel_less resource_preordering.strict_trans)

  have assum1': \<open>(\<Union>a\<in>A. {a} + C) = A\<close>
    using assms
    by (metis plus_set_eq_plus_left_members)
  then have A_always_descending: \<open>\<forall>x\<in>A. \<exists>y\<in>A. y \<prec> x\<close>
    using Crel_def Crel_less never_punit_C
    by blast

  have H1: \<open>\<forall>a\<in>A. \<forall>b\<in>{a} + C. a \<prec> b\<close>
    using never_punit_C Crel_def Crel_less by blast

  have H2: \<open>\<forall>a\<in>A. (\<exists>c\<in>C. a ## c) \<longrightarrow> (\<exists>a'\<in>A. a \<prec> a')\<close>
    using assum1' H1
    by (fastforce simp add: set_eq_iff singleton_plus_set_eq Bex_def Ball_def)

  let ?R = \<open>{x. \<exists>a\<in>A. \<exists>a'\<in>A. a ## x \<and> a' = a + x \<and> a \<noteq> a'}\<close>

  have \<open>C \<subseteq> ?R\<close>
    using Cpunit C_reduced never_punit_C
    by (fastforce simp add: plus_set_def Ball_def Bex_def)

  have \<open>A + C1 = A \<longrightarrow> (\<forall>a\<in>A. a \<notin> {a} + C1) \<longrightarrow> C1 \<subseteq> ?R\<close>
    using assmsP1(2)
    by (fastforce simp add: plus_set_def)

  show \<open>A + C1 = A\<close>
    oops


lemma minset_positivity_sep_alg:
  fixes A :: \<open>('a::sep_alg) set\<close>
  assumes split_punit_add: \<open>A + (C1 + C2) = A\<close>
    and minAs:\<open>\<forall>a\<in>A. \<exists>la\<in>A. la \<preceq> a \<and> (\<forall>a'\<in>A. \<not> a' \<prec> la)\<close>
  shows \<open>A + C1 = A\<close>
  using assms(1)
    minset_sepadd_unit_set_contains_unit[OF split_punit_add minAs]
  apply (clarsimp simp add: set_eq_iff plus_set_def Ball_def Bex_def)
  apply (rule iffI)
    (* \<Rightarrow> *)
   apply clarsimp
   apply (rename_tac a c1)
   apply (drule spec, drule mp, assumption)
   apply (elim exE conjE)
   apply clarsimp
   apply (rename_tac c1' c2')
   apply (subgoal_tac \<open>a + c1' = a\<close>)
    prefer 2
    apply (metis disjoint_add_rightL disjoint_add_swap_rl unit_sub_closure2)
   apply (subgoal_tac \<open>a + (c1 + c2') \<in> A\<close>)
    prefer 2
    apply (metis disjoint_add_rightR disjoint_add_swap_lr2 disjoint_sym_iff partial_add_assoc3)
   apply (drule_tac x=\<open>a\<close> in spec)
   apply clarsimp
   apply (metis disjoint_add_rightR disjoint_sym partial_add_assoc3 partial_add_assoc_commute_right)
    (* \<Leftarrow> *)
  apply (metis disjoint_add_rightL disjoint_add_swap_rl unit_sub_closure2)
  done

section \<open> minsets \<close>

abbreviation (in perm_alg) \<open>min_of A y \<equiv> \<forall>z\<in>A. \<not> z \<prec> y\<close>
abbreviation (in perm_alg) "has_min_elems A \<equiv> \<forall>x\<in>A. \<exists>y\<in>A. y \<preceq> x \<and> min_of A y"

typedef(overloaded) ('a::perm_alg) 
  mset = 
  \<open>{ A::'a set. has_min_elems A}\<close>
  using sepequivs_def by auto

print_theorems
setup_lifting type_definition_mset


lift_definition mset_mins :: \<open>('a::perm_alg) mset \<Rightarrow> 'a set\<close> is
  \<open>\<lambda>A. {x\<in>A. \<forall>z\<in>A. \<not> z \<prec> x}\<close> .

lift_definition mset_mins_of :: \<open>('a::perm_alg) mset \<Rightarrow> 'a \<Rightarrow> 'a set\<close> is
  \<open>\<lambda>A a. {x\<in>A. x \<preceq> a \<and> (\<forall>z\<in>A. \<not> z \<prec> x)}\<close> .

lemma mins_of_all_eq_mins:
  \<open>\<Union>(mset_mins_of A ` Rep_mset A) = mset_mins A\<close>
  by (transfer, force)

lift_definition mset_member :: \<open>('a::perm_alg) \<Rightarrow> 'a mset \<Rightarrow> bool\<close> (infix \<open>\<in>\<^sub>M\<close> 55) is
  \<open>(\<in>)\<close> .

lift_definition mset_subseteq :: \<open>('a::perm_alg) mset \<Rightarrow> 'a mset \<Rightarrow> bool\<close> (infix \<open>\<subseteq>\<^sub>M\<close> 55) is
  \<open>(\<subseteq>)\<close> .

lemma mset_antisym:
  \<open>A \<subseteq>\<^sub>M B \<Longrightarrow> B \<subseteq>\<^sub>M A \<Longrightarrow> A = B\<close>
  by (simp add: Rep_mset_inject mset_subseteq.rep_eq)


lemma (in perm_alg) sepadd_right_addmono:
  \<open>a ## c \<Longrightarrow> a + x ## c \<Longrightarrow> a ## x \<Longrightarrow> a + c + x = a + x + c\<close>
  using disjoint_add_leftR disjoint_add_left_commute2 partial_add_right_commute
  by blast+

lemma (in perm_alg) disjoint22_commute23:
  \<open>a ## c \<Longrightarrow> b ## d \<Longrightarrow> a + c ## b + d \<Longrightarrow> a + b ## c + d\<close>
  by (meson disjoint_add_rightL disjoint_add_swap_rl disjoint_middle_swap)

lemma (in perm_alg) sepadd22_commute23:
  \<open>a ## c \<Longrightarrow> b ## d \<Longrightarrow> a + c ## b + d \<Longrightarrow> a + c + (b + d) = a + b + (c + d)\<close>
  by (metis disjoint_add_rightR disjoint_add_swap_lr disjoint_sym partial_add_double_assoc)

lemma (in perm_alg) resource_order_parts_leq_then_add_leq:
  assumes
    \<open>a' \<preceq> a\<close>
    \<open>b' \<preceq> b\<close>
    \<open>a ## b\<close>
  shows
    \<open>a' + b' \<preceq> a + b\<close>
  using assms
  by (meson disjoint_preservation disjoint_preservation2 resource_preordering.trans
      sepadd_left_mono sepadd_right_mono)

context perm_alg
begin

definition res_step :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>res_step a b \<equiv> a \<prec> b \<and> (\<forall>x. a \<preceq> x \<longrightarrow> \<not> x \<preceq> b)\<close>

end

(*
lemma (in perm_alg) countable_resource_leq_induct:
  fixes a b :: 'a
  assumes countable: \<open>\<And>a b::'a. a \<preceq> b \<Longrightarrow> res_step\<^sup>*\<^sup>* a b\<close>
  assumes leq: \<open>a \<preceq> b\<close>
  assumes Pa: \<open>P a\<close>
  assumes step: \<open>(\<And>y z. a \<preceq> y \<Longrightarrow> res_step y z \<Longrightarrow> P y \<Longrightarrow> P z)\<close>
  shows \<open>P b\<close>
  using assms rtranclp_induct[OF countable, of a b]
  by (meson res_step_def resource_ordering.refl resource_order.less_imp_le)
*)

lemma (in perm_alg)
  assumes countable: \<open>\<And>a b::'a. a \<preceq> b \<Longrightarrow> res_step\<^sup>*\<^sup>* a b\<close>
  shows
  \<open>\<forall>x\<in>A. \<exists>y\<in>A. y \<preceq> x \<and> min_of A y \<Longrightarrow>
    \<forall>x\<in>B. \<exists>y\<in>B. y \<preceq> x \<and> min_of B y \<Longrightarrow>
    L = {(x,y). x \<prec> y} \<Longrightarrow>
    MA = {x\<in>A. min_of A x} \<Longrightarrow>
    MB = {x\<in>B. min_of B x} \<Longrightarrow>
    MAB = {x+y|x y. x ## y \<and> x \<in> MA \<and> y \<in> MB} \<Longrightarrow>
    \<exists>ma\<in>A. \<exists>mb\<in>B. min_of A ma \<and> min_of B mb \<and> ma ## mb \<Longrightarrow>
    \<exists>ma\<in>A. \<exists>mb\<in>B.
      min_of A ma \<and> min_of B mb \<and> ma ## mb \<and>
      (\<forall>x\<in>A. min_of A x \<longrightarrow> (\<forall>y\<in>B. min_of B y \<longrightarrow> x ## y \<longrightarrow> \<not> x + y \<prec> ma + mb))\<close>
  apply -
  apply (clarsimp simp add: Ball_def Bex_def)
  apply (rename_tac ma mb)
  apply (rule ccontr)
  apply clarsimp
  oops


lemma
  fixes A B :: \<open>('a :: disjoint_parts_perm_alg) set\<close>
  shows
  \<open>L = {(a::'a,b). a \<lesssim> b} \<Longrightarrow>
    R = {(a::'a,b,a + b)|a b. a ## b} \<Longrightarrow>
    \<forall>x\<in>A. \<exists>y\<in>A. y \<preceq> x \<and> (\<forall>z\<in>A. \<not> z \<prec> y) \<Longrightarrow>
    \<forall>x\<in>B. \<exists>y\<in>B. y \<preceq> x \<and> (\<forall>z\<in>B. \<not> z \<prec> y) \<Longrightarrow>
    MA = {y\<in>A. \<forall>z\<in>A. \<not> z \<prec> y} \<Longrightarrow>
    MB = {y\<in>B. \<forall>z\<in>B. \<not> z \<prec> y} \<Longrightarrow>
    MAB = MA + MB \<Longrightarrow>
    a \<in> A \<Longrightarrow>
    b \<in> B \<Longrightarrow>
    a ## b \<Longrightarrow>
    \<forall>x\<in>MAB. \<exists>y\<in>MAB. y \<preceq> x \<and> (\<forall>z\<in>MAB. \<not> z \<prec> y)\<close>
  apply (clarsimp simp add: plus_set_def Bex_def Ball_def)
  apply (rename_tac ma mb)
  oops

lemma (in perm_alg) min_sepadd_preservation:
  \<open>L = {(a,b). a \<prec> b} \<Longrightarrow>
    \<forall>x\<in>A. \<exists>y\<in>A. \<forall>z\<in>A. \<not> z \<prec> y \<Longrightarrow>
    \<forall>x\<in>B. \<exists>y\<in>B. \<forall>z\<in>B. \<not> z \<prec> y \<Longrightarrow>
    a \<in> A \<Longrightarrow>
    b \<in> B \<Longrightarrow>
    a ## b \<Longrightarrow>
    (\<exists>x'\<in>A. (\<forall>z\<in>A. \<not> z \<prec> x') \<and>
      (\<exists>y'\<in>B. (\<forall>z\<in>B. \<not> z \<prec> y') \<and>
        x' ## y' \<and> (\<forall>za\<in>A. \<forall>zb\<in>B. za ## zb \<longrightarrow> \<not> za + zb \<prec> x' + y')
      ))\<close>
  
  oops


lemma (in perm_alg)
  \<open>L = {(a,b). a \<prec> b} \<Longrightarrow>
    (##) = (\<lambda>_ _. True) \<Longrightarrow>
    min_of A a \<Longrightarrow> min_of A b \<Longrightarrow> min_of A c \<Longrightarrow>
      a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + c \<preceq> b + c \<or> b + c \<preceq> a + c\<close>
  nitpick
  oops

lemma (in cancel_perm_alg) cancel_lessL:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> a + b \<prec> a + c \<Longrightarrow> b \<prec> c\<close>
  apply (clarsimp simp add: less_sepadd_def')
  apply (metis disjoint_add_leftR partial_add_assoc_rev partial_left_cancel2D)
  done


lemma helper00:
  fixes A :: \<open>('a::cancel_perm_alg) set\<close>
  shows
  \<open>\<forall>x\<in>A. min_of A x \<Longrightarrow>
   a \<in> A \<Longrightarrow>
   a ## x \<Longrightarrow>
   \<exists>b. b \<in> A \<and> x ## b \<and> (\<forall>b'. b' \<in> A \<longrightarrow> x ## b' \<longrightarrow> \<not> x + b' \<prec> x + b)\<close>
  by (meson cancel_lessL disjoint_sym)

lemma helper0:
  fixes A :: \<open>('a::cancel_perm_alg) set\<close>
  assumes
    \<open>\<forall>x\<in>A. min_of A x\<close>
    (* \<open>(\<And>a. a \<in> A \<Longrightarrow> \<exists>x\<in>A. x \<preceq> a \<and> min_of A x)\<close> *)
    \<open>a \<in> A\<close>
    \<open>a ## x\<close>
  shows \<open>\<exists>z. z \<in> {x} + A \<and> min_of ({x} + A) z\<close>
  using assms
  by (clarsimp simp add: plus_set_def)
    (metis cancel_lessL disjoint_sym)

lemma disj_imp_rev:
  \<open>P \<or> Q \<longleftrightarrow> \<not> Q \<longrightarrow> P\<close>
  by blast

lemma ball_imp_bex_compose_helper:
  \<open>(\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c) \<Longrightarrow>
    \<forall>x\<in>A. P x w \<longrightarrow> Q x \<longrightarrow> (\<exists>y\<in>B. P y x \<and> Q y) \<Longrightarrow>
    (\<forall>x\<in>B. P x w \<longrightarrow> Q x \<longrightarrow> (\<exists>y\<in>C. P y x \<and> Q y)) \<Longrightarrow>
    \<forall>x\<in>A. P x w \<longrightarrow> Q x \<longrightarrow> (\<exists>y\<in>C. P y x \<and> Q y)\<close>
  by blast


lemma minset_un:
  fixes A B :: \<open>('a::perm_alg) set\<close>
  assumes
    \<open>(\<And>a. a \<in> A \<Longrightarrow> \<exists>x\<in>A. x \<preceq> a \<and> min_of A x)\<close>
    \<open>(\<And>b. b \<in> B \<Longrightarrow> \<exists>x\<in>B. x \<preceq> b \<and> min_of B x)\<close>
    \<open>x \<in> A \<union> B\<close>
  shows \<open>\<exists>y\<in>A\<union>B. y \<preceq> x \<and> min_of (A \<union> B) y\<close>
  using assms(3)
  apply -
  apply (rule ccontr)
  apply (clarsimp simp add: ball_Un)
  apply (subgoal_tac \<open>\<forall>y\<in>A. y \<preceq> x \<longrightarrow> min_of A y \<longrightarrow> (\<exists>z\<in>B. z \<prec> y \<and> min_of B z)\<close>)
   prefer 2
   apply (metis assms(1-2) resource_order.le_less resource_preordering.strict_trans1)
  apply (thin_tac \<open>\<forall>x\<in>_. _ x\<close>)
  apply (subgoal_tac \<open>\<forall>y\<in>B. y \<preceq> x \<longrightarrow> min_of B y \<longrightarrow> (\<exists>z\<in>A. z \<prec> y \<and> min_of A z)\<close>)
   prefer 2
   apply (metis assms(1-2) resource_order.le_less resource_preordering.strict_trans1)
  apply (thin_tac \<open>\<forall>x\<in>_. _ x\<close>)
  apply (subgoal_tac \<open>\<forall>y\<in>B. y \<preceq> x \<longrightarrow> min_of B y \<longrightarrow> (\<exists>z\<in>B. z \<prec> y \<and> min_of B z)\<close>)
   prefer 2
   apply clarsimp
   apply (drule bspec, assumption, metis resource_order.le_less resource_preordering.strict_trans)
  apply (subgoal_tac \<open>\<forall>y\<in>A. y \<preceq> x \<longrightarrow> min_of A y \<longrightarrow> (\<exists>z\<in>A. z \<prec> y \<and> min_of A z)\<close>)
   prefer 2
   apply clarsimp
   apply (drule bspec, assumption, metis resource_order.le_less resource_preordering.strict_trans)
  apply (metis assms(1-2))
  done

lemma no_minset_rat_fperm:
  fixes x :: \<open>rat fperm\<close>
  shows \<open>\<not> min_of UNIV x\<close>
  apply (clarsimp simp add: Bex_def less_sepadd_def)
  apply transfer
  apply clarsimp
  apply (rule_tac x=\<open>x/2\<close> in exI)
  apply clarsimp
  apply (rule_tac x=\<open>x/2\<close> in exI)
  apply clarsimp
  done

lemma minset_Un:
  fixes A B :: \<open>('a::perm_alg) set\<close>
  assumes
    \<open>(\<And>A a. A \<in> \<AA> \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>x\<in>A. x \<preceq> a \<and> min_of A x)\<close>
    \<open>x \<in> \<Union>\<AA>\<close>
  shows \<open>\<exists>y\<in>\<Union>\<AA>. y \<preceq> x \<and> min_of (\<Union>\<AA>) y\<close>
  oops (* counterexample above *)



lemma thegoal:
  fixes A B :: \<open>('a::cancel_perm_alg) set\<close>
  shows
    \<open>(\<And>a. a \<in> A \<Longrightarrow> \<exists>x\<in>A. x \<preceq> a \<and> min_of A x) \<Longrightarrow>
      (\<And>b. b \<in> B \<Longrightarrow> \<exists>x\<in>B. x \<preceq> b \<and> min_of B x) \<Longrightarrow>
      a \<in> A \<Longrightarrow>
      b \<in> B \<Longrightarrow>
      a ## b \<Longrightarrow>
      \<exists>x. (\<exists>a b. x = a + b \<and> a \<in> A \<and> b \<in> B \<and> a ## b) \<and>
             x \<preceq> a + b \<and> (\<forall>z. (\<exists>a b. z = a + b \<and> a \<in> A \<and> b \<in> B \<and> a ## b) \<longrightarrow> \<not> z \<prec> x)\<close>
  oops

lemma helper2:
  fixes A B :: \<open>('a::perm_alg) set\<close>
  shows
  \<open>(\<And>a. a \<in> A \<Longrightarrow> \<exists>x\<in>A. x \<preceq> a \<and> min_of A x) \<Longrightarrow>
   (\<And>b. b \<in> B \<Longrightarrow> \<exists>x\<in>B. x \<preceq> b \<and> min_of B x) \<Longrightarrow>
    c \<in> A + B \<Longrightarrow>
    min_of (A + B) c \<Longrightarrow> (\<exists>a\<in>A. \<exists>b\<in>B. min_of A a \<and> min_of B b \<and> a ## b \<and> c = a + b)\<close>
  sorry

lemma thegoal:
  fixes A B :: \<open>('a::perm_alg) set\<close>
  shows
    \<open>(\<And>a. a \<in> A \<Longrightarrow> \<exists>x\<in>A. x \<preceq> a \<and> min_of A x) \<Longrightarrow>
      (\<And>b. b \<in> B \<Longrightarrow> \<exists>x\<in>B. x \<preceq> b \<and> min_of B x) \<Longrightarrow>
      a \<in> A \<Longrightarrow>
      b \<in> B \<Longrightarrow>
      a ## b \<Longrightarrow>
      \<exists>x. (\<exists>a b. x = a + b \<and> a \<in> A \<and> b \<in> B \<and> a ## b) \<and>
             x \<preceq> a + b \<and> (\<forall>z. (\<exists>a b. z = a + b \<and> a \<in> A \<and> b \<in> B \<and> a ## b) \<longrightarrow> \<not> z \<prec> x)\<close>
  sorry

(*
instantiation mset :: (multiunit_sep_alg) perm_alg
begin

lift_definition plus_mset :: \<open>('a::multiunit_sep_alg) mset \<Rightarrow> 'a mset \<Rightarrow> 'a mset\<close> is
  \<open>\<lambda>A B. {a + b|a b. a \<in> A \<and> b \<in> B \<and> a ## b}\<close>
  apply (clarsimp simp add: Bex_def)
  apply (rename_tac A B a b)
  apply (drule_tac x=a in meta_spec)
  apply (drule_tac x=b in meta_spec)
  apply clarsimp
  apply (rename_tac am bm)
  apply(cut_tac a=am and b=bm and c=a and d=b in sepadd_mono, simp_all) 
   apply (meson disjoint_preservation disjoint_preservation2)
  apply (rule_tac x=\<open>am + bm\<close> in exI) 
  apply (rule conjI) 
   apply (metis disjoint_preservation disjoint_preservation2)
  apply clarsimp
  oops

lift_definition disjoint_mset :: \<open>('a::multiunit_sep_alg) mset \<Rightarrow> 'a mset \<Rightarrow> bool\<close> is
  \<open>\<lambda>A B. True\<close> .

instance
  apply standard
       apply transfer
  oops
      apply (transfer, force)
     apply (transfer, force)
    apply (transfer, force)
   apply (transfer, force)
  apply clarsimp
  apply (transfer)
  apply force
  done

end
*)


instantiation set :: (pre_perm_alg) pre_perm_alg
begin

(* Already defined
definition plus_set :: \<open>('a::pre_perm_alg) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>plus_set A B \<equiv> {a + b|a b. a \<in> A \<and> b \<in> B \<and> a ## b}\<close>
*)

definition disjoint_set :: \<open>('a::pre_perm_alg) set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>disjoint_set A B \<equiv> True\<close>
declare disjoint_set_def[simp]

instance
  apply standard
      apply (clarsimp simp add: plus_set_def set_eq_iff, rule iffI)
       apply (metis disjoint_add_leftR disjoint_add_swap_lr partial_add_assoc2)
      apply (metis disjoint_add_rightL disjoint_add_swap_rl partial_add_assoc3)
     apply (clarsimp simp add: plus_set_def set_eq_iff)
     apply (meson disjoint_sym partial_add_commute)
    apply (simp; fail)
   apply (simp; fail)
  apply (simp; fail)
  done

end


end
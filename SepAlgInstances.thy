theory SepAlgInstances
  imports SepLogic HOL.Rat "HOL-Library.Product_Order" "HOL-Library.Product_Plus"
begin


section \<open> Product \<close>

declare plus_prod_def[simp]

declare zero_prod_def[simp]

subsection \<open> perm_alg \<close>

instantiation prod :: (pre_perm_alg,pre_perm_alg) pre_perm_alg
begin

definition disjoint_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod a b \<equiv> (fst a ## fst b \<and> snd a ## snd b)\<close>
declare disjoint_prod_def[simp]

instance
  apply standard
      apply (force simp add: partial_add_assoc)
     apply (force dest: partial_add_commute)
    apply (force simp add: disjoint_sym_iff)
   apply (force dest: disjoint_add_rightL)
  apply (force dest: disjoint_add_right_commute)
  done

end

instance prod :: (perm_alg,perm_alg) perm_alg
  by standard (force dest: positivity)

lemma less_eq_sepadd_prod_eq:
  \<open>a \<preceq> b \<longleftrightarrow> fst a = fst b \<and> snd a = snd b \<or> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: less_eq_sepadd_def part_of_def)

lemma part_of_prod_eq:
  \<open>a \<lesssim> b \<longleftrightarrow> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: part_of_def)

lemma less_sepadd_prod_eq:
  fixes a b :: \<open>'a::pre_perm_alg \<times> 'b::pre_perm_alg\<close>
  shows \<open>a \<prec> b \<longleftrightarrow>
          (fst a \<noteq>  fst b \<or> snd a \<noteq> snd b) \<and>
          fst a \<lesssim> fst b \<and>
          snd a \<lesssim> snd b \<and>
          (\<not> fst b \<lesssim> fst a \<or> \<not> snd b \<lesssim> snd a)\<close>
  by (cases a; cases b; auto simp add: less_sepadd_def part_of_def)


subsection \<open> mu_sep_alg \<close>

instantiation prod :: (pre_multiunit_sep_alg,pre_multiunit_sep_alg) pre_multiunit_sep_alg
begin

lemma less_sepadd_prod_eq2[simp]:
  fixes a :: \<open>'a \<times> 'b\<close>
  shows \<open>a \<prec> b \<longleftrightarrow> (fst a \<prec> fst b \<and> snd a \<preceq> snd b \<or> fst a \<preceq> fst b \<and> snd a \<prec> snd b)\<close>
  apply (cases a, cases b)
  apply (clarsimp simp add: less_eq_sepadd_def less_sepadd_def' part_of_def less_sepadd_prod_eq)
  apply (metis le_iff_sepadd less_eq_sepadd_def resource_preordering.strict_iff_not)
  done

lemma less_eq_sepadd_prod_eq2[simp]:
  fixes a :: \<open>'a \<times> 'b\<close>
  shows \<open>a \<preceq> b \<longleftrightarrow> fst a \<preceq> fst b \<and> snd a \<preceq> snd b\<close>
  by (cases a, cases b, clarsimp simp add: less_eq_sepadd_def,
      metis unitof_disjoint2 unitof_is_unitR2)

definition unitof_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>unitof \<equiv> map_prod unitof unitof\<close>
declare unitof_prod_def[simp]

instance
  by standard (simp add: less_eq_sepadd_def)+

end

subsection \<open> sep_alg \<close>

instantiation prod :: (multiunit_sep_alg,multiunit_sep_alg) multiunit_sep_alg
begin
instance by standard (simp add: fun_eq_iff)+
end

instantiation prod :: (sep_alg,sep_alg) sep_alg
begin

declare bot_prod_def[simp]
instance by standard (simp add: fun_eq_iff)+

end

lemma prod_sepadd_unit_iff[simp]:
  \<open>sepadd_unit (a, b) \<longleftrightarrow> sepadd_unit a \<and> sepadd_unit b\<close>
  by (simp add: sepadd_unit_def, force)

subsection \<open> Extended instances \<close>

instance prod :: (dupcl_perm_alg, dupcl_perm_alg) dupcl_perm_alg
  by standard (force dest: dup_sub_closure)

(* not an allcompatible_perm_alg *)

instance prod :: (strong_sep_pre_perm_alg, strong_sep_pre_perm_alg) strong_sep_pre_perm_alg
  by standard (clarsimp simp add: selfsep_iff)

instance prod :: (disjoint_parts_pre_perm_alg, disjoint_parts_pre_perm_alg) disjoint_parts_pre_perm_alg
  by standard simp

instance prod :: (trivial_selfdisjoint_pre_perm_alg, trivial_selfdisjoint_pre_perm_alg) trivial_selfdisjoint_pre_perm_alg
  by standard (clarsimp, meson selfdisjoint_same)

instance prod :: (crosssplit_pre_perm_alg, crosssplit_pre_perm_alg) crosssplit_pre_perm_alg
  apply standard
  apply clarsimp
  apply (rename_tac a x b y c z d w)
  apply (frule(2) cross_split[of \<open>_::'a\<close>])
  apply (frule(2) cross_split[of \<open>_::'b\<close>])
  apply clarsimp
  apply metis
  done

instance prod :: (cancel_pre_perm_alg, cancel_pre_perm_alg) cancel_pre_perm_alg
  by standard force

text \<open>
  This instance is troublesome. We have that if either the left
  or the right lacks a unit, then the entire instance will lack a unit.
  However, Isabelle's typeclasses will now allow multiple instances,
  even when the instance is completely logical. (I.e. there are no new definitions.)

  We pick a right biased implementation, to match the default associativity of prod.
  This means that permissions must be placed on the *right* of a tuple if we want to derive
  instances like the cancellativity of munit heaps automatically.
\<close>
instance prod :: (perm_alg, no_unit_pre_perm_alg) no_unit_pre_perm_alg
  by (standard) (metis no_units split_pairs2 prod_sepadd_unit_iff)

instantiation prod :: (halfof, halfof) halfof
begin
definition \<open>halfof_prod \<equiv> \<lambda>(a,b). (halfof a, halfof b)\<close>
declare halfof_prod_def[simp]
instance ..
end

instance prod :: (halving_pre_perm_alg, halving_pre_perm_alg) halving_pre_perm_alg
  apply standard
    apply (simp add: halfof_additive_split split_beta; fail)
   apply (simp add: halfof_self_disjoint split_beta; fail)
  apply (simp add: halfof_sepadd_distrib split_beta; fail)
  done

instance prod :: (all_disjoint_pre_perm_alg, all_disjoint_pre_perm_alg) all_disjoint_pre_perm_alg
  by standard simp


subsection \<open> add_fst & add_snd for tuple perm_alg \<close>

lemma perm_alg_plus_fst_accum[simp]:
  fixes x :: \<open>'a :: perm_alg\<close>
  shows \<open>fst xy ## x \<Longrightarrow> fst xy ## x' \<Longrightarrow> x ## x' \<Longrightarrow> (xy +\<^sub>L x) +\<^sub>L x' = xy +\<^sub>L (x + x')\<close>
  by (cases xy, simp add: partial_add_assoc)

lemma perm_alg_plus_snd_accum[simp]:
  fixes y :: \<open>'a :: perm_alg\<close>
  shows \<open>snd xy ## y \<Longrightarrow> snd xy ## y' \<Longrightarrow> y ## y' \<Longrightarrow> (xy +\<^sub>R y) +\<^sub>R y' = xy +\<^sub>R (y + y')\<close>
  by (cases xy, simp add: partial_add_assoc)

lemma perm_alg_plus_fst_plus_snd_eq[simp]:
  fixes y :: \<open>'a :: perm_alg\<close>
  shows
    \<open>xy +\<^sub>L x +\<^sub>R y = xy + (x, y)\<close>
    \<open>xy +\<^sub>R y +\<^sub>L x = xy + (x, y)\<close>
  by simp+


subsubsection \<open> Sepconj-conj \<close>

definition sepconj_conj
  :: \<open>('a::pre_perm_alg \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<^emph>\<and>\<close> 70) where
  \<open>p \<^emph>\<and> q \<equiv> \<lambda>h. \<exists>a b c. a ## b \<and> h = (a + b, c) \<and> p (a, c) \<and> q (b, c)\<close>

\<comment> \<open> Not simp by default. \<close>
lemma sepconj_conj_apply:
  \<open>(p \<^emph>\<and> q) (ls, ss) = (\<exists>la lb. la ## lb \<and> ls = la + lb \<and> p (la, ss) \<and> q (lb, ss))\<close>
  by (simp add: sepconj_conj_def)

lemma sepconj_conj_apply2:
  \<open>(p \<^emph>\<and> q) s = (\<exists>la lb. la ## lb \<and> fst s = la + lb \<and> p (la, snd s) \<and> q (lb, snd s))\<close>
  by (simp add: sepconj_conj_def, metis fst_conv snd_conv surjective_pairing)

lemma sepconj_conjI:
  \<open>p (a, y) \<Longrightarrow> q (b, y) \<Longrightarrow> a ## b \<Longrightarrow> x = a + b \<Longrightarrow> (p \<^emph>\<and> q) (x, y)\<close>
  by (force simp add: sepconj_conj_def)

lemma sepconj_conj_revI:
  \<open>p (b, y) \<Longrightarrow> q (a, y) \<Longrightarrow> a ## b \<Longrightarrow> x = a + b \<Longrightarrow> (p \<^emph>\<and> q) (x, y)\<close>
  by (force simp add: sepconj_conj_def disjoint_sym_iff partial_add_commute)

lemma sepconj_conj_assoc:
  \<open>(p \<^emph>\<and> q) \<^emph>\<and> r = p \<^emph>\<and> (q \<^emph>\<and> r)\<close>
  apply (clarsimp simp add: sepconj_conj_def fun_eq_iff)
  apply (rule iffI)
   apply (metis disjoint_add_leftR disjoint_add_swap_lr partial_add_assoc2)
  apply (metis disjoint_add_rightL disjoint_add_swap_rl partial_add_assoc3)
  done

lemma sepconj_conj_mono:
  \<open>p \<le> p' \<Longrightarrow> q \<le> q' \<Longrightarrow> p \<^emph>\<and> q \<le> p' \<^emph>\<and> q'\<close>
  by (force simp add: sepconj_conj_def)

lemma sepconj_conj_monoL:
  \<open>p \<le> p' \<Longrightarrow> p \<^emph>\<and> q \<le> p' \<^emph>\<and> q\<close>
  by (force simp add: sepconj_conj_def)

lemma sepconj_conj_monoR:
  \<open>q \<le> q' \<Longrightarrow> p \<^emph>\<and> q \<le> p \<^emph>\<and> q'\<close>
  by (force simp add: sepconj_conj_def)


subsubsection \<open> Sepimp-imp \<close>

definition sepimp_conj
  :: \<open>('a::pre_perm_alg \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<midarrow>\<^emph>\<^sub>\<and>\<close> 61) where
  \<open>p \<midarrow>\<^emph>\<^sub>\<and> q \<equiv> \<lambda>(x,y). \<forall>x1. x ## x1 \<longrightarrow> p (x1, y) \<longrightarrow> q (x + x1, y)\<close>

lemma sepimp_conjI:
  \<open>(\<And>x1. x ## x1 \<Longrightarrow> p (x1, y) \<Longrightarrow> q (x + x1, y)) \<Longrightarrow> (p \<midarrow>\<^emph>\<^sub>\<and> q) (x, y)\<close>
  by (simp add: sepimp_conj_def)

lemma sepimp_conj_apply:
  \<open>(p \<midarrow>\<^emph>\<^sub>\<and> q) (x, y) = (\<forall>x1. x ## x1 \<longrightarrow> p (x1, y) \<longrightarrow> q (x + x1, y))\<close>
  by (simp add: sepimp_conj_def)

lemma sepimp_conj_sepconj_conjL:
  \<open>(p \<^emph>\<and> q \<midarrow>\<^emph>\<^sub>\<and> r) = (p \<midarrow>\<^emph>\<^sub>\<and> q \<midarrow>\<^emph>\<^sub>\<and> r)\<close>
  apply (clarsimp simp add: sepconj_conj_def sepimp_conj_def fun_eq_iff)
  apply (rule iffI)
   apply (metis disjoint_add_leftR disjoint_add_swap_lr partial_add_assoc2)
  apply (metis disjoint_add_rightL disjoint_add_swap_rl partial_add_assoc3)
  done

lemma sepimp_conj_mono:
  \<open>p' \<le> p \<Longrightarrow> q \<le> q' \<Longrightarrow> p \<midarrow>\<^emph>\<^sub>\<and> q \<le> p' \<midarrow>\<^emph>\<^sub>\<and> q'\<close>
  by (force simp add: sepimp_conj_def)

lemma sepconj_conj_sepimp_conj_shunt:
  \<open>p \<^emph>\<and> q \<le> r \<longleftrightarrow> p \<le> q \<midarrow>\<^emph>\<^sub>\<and> r\<close>
  by (force simp add: sepconj_conj_def sepimp_conj_def le_fun_def)

lemmas sepimp_conj_sepconj_conj_shunt = sepconj_conj_sepimp_conj_shunt[symmetric]


subsubsection \<open> septraction-conj \<close>

definition septract_conj
  :: \<open>('a::pre_perm_alg \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<midarrow>\<odot>\<^sub>\<and>\<close> 62) where
  \<open>p \<midarrow>\<odot>\<^sub>\<and> q \<equiv> \<lambda>(x, y). \<exists>xb. x ## xb \<and> p (xb, y) \<and> q (x + xb, y)\<close>

lemma septract_conjI:
  \<open>x ## xb \<Longrightarrow> p (xb, y) \<Longrightarrow> q (x + xb, y) \<Longrightarrow> (p \<midarrow>\<odot>\<^sub>\<and> q) (x, y)\<close>
  by (force simp add: septract_conj_def)

lemma septract_conj_apply:
  \<open>(p \<midarrow>\<odot>\<^sub>\<and> q) (x, y) = (\<exists>xb. x ## xb \<and> p (xb, y) \<and> q (x + xb, y))\<close>
  by (simp add: septract_conj_def)

lemma septract_conj_mono:
  \<open>p \<le> p' \<Longrightarrow> q \<le> q' \<Longrightarrow> p \<midarrow>\<odot>\<^sub>\<and> q \<le> p' \<midarrow>\<odot>\<^sub>\<and> q'\<close>
  by (force simp add: septract_conj_def le_fun_def)


subsubsection \<open> sepcoimp-conj \<close>

definition sepcoimp_conj
  :: \<open>('a::pre_perm_alg \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<sim>\<^emph>\<^sub>\<and>\<close> 62) where
  \<open>p \<sim>\<^emph>\<^sub>\<and> q \<equiv> \<lambda>(x, y). \<forall>xa xb. xa ## xb \<longrightarrow> x = xa + xb \<longrightarrow> p (xa, y) \<longrightarrow> q (xb, y)\<close>

lemma sepcoimp_conjI:
  \<open>(\<And>xa xb. xa ## xb \<Longrightarrow> x = xa + xb \<Longrightarrow> p (xa, y) \<Longrightarrow> q (xb, y)) \<Longrightarrow> (p \<sim>\<^emph>\<^sub>\<and> q) (x, y)\<close>
  by (force simp add: sepcoimp_conj_def)

lemma sepcoimp_conj_apply:
  \<open>(p \<sim>\<^emph>\<^sub>\<and> q) (x, y) = (\<forall>xa xb. xa ## xb \<longrightarrow> x = xa + xb \<longrightarrow> p (xa, y) \<longrightarrow> q (xb, y))\<close>
  by (simp add: sepcoimp_conj_def)

lemma sepcoimp_conj_mono:
  \<open>p' \<le> p \<Longrightarrow> q \<le> q' \<Longrightarrow> p \<sim>\<^emph>\<^sub>\<and> q \<le> p' \<sim>\<^emph>\<^sub>\<and> q'\<close>
  by (force simp add: sepcoimp_conj_def le_fun_def)


section \<open> (additive) unit \<close>

instantiation unit :: perm_alg
begin

definition plus_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> unit\<close> where
  \<open>plus_unit a b \<equiv> ()\<close>
declare plus_unit_def[simp]

definition disjoint_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> bool\<close> where
  \<open>disjoint_unit a b \<equiv> True\<close>
declare disjoint_unit_def[simp]

instance
  by standard simp+

end

instantiation unit :: multiunit_sep_alg
begin

definition unitof_unit :: \<open>unit \<Rightarrow> unit\<close> where
  \<open>unitof_unit \<equiv> \<lambda>_. ()\<close>
declare unitof_unit_def[simp]

instance
  by standard force+

end

instantiation unit :: sep_alg
begin

definition zero_unit :: \<open>unit\<close> where
  \<open>zero_unit \<equiv> ()\<close>
declare zero_unit_def[simp]

definition bot_unit :: \<open>unit\<close> where
  \<open>bot_unit \<equiv> ()\<close>
declare bot_unit_def[simp]

instance
  by standard simp+

end

subsection \<open> Extended instances \<close>

instance unit :: dupcl_perm_alg
  by standard simp

instance unit :: allcompatible_perm_alg
  by standard simp

instance unit :: strong_sep_pre_perm_alg
  by standard simp

instance unit :: disjoint_parts_pre_perm_alg
  by standard simp

instance unit :: trivial_selfdisjoint_pre_perm_alg
  by standard simp

instance unit :: crosssplit_pre_perm_alg
  by standard simp

instance unit :: cancel_pre_perm_alg
  by standard simp

(* not a no_unit_pre_perm_alg *)

instantiation unit :: halving_pre_perm_alg
begin
definition \<open>halfof_unit \<equiv> \<lambda>_::unit. ()\<close>
declare halfof_unit_def[simp]
instance by standard simp+
end

instance unit :: all_disjoint_pre_perm_alg
  by standard simp


section \<open> Sum \<close>

subsection \<open> order \<close>

instantiation sum :: (order, order) order
begin

definition less_eq_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_sum a b \<equiv>
    (\<exists>x y. a = Inl x \<and> b = Inl y \<and> x \<le> y) \<or>
    (\<exists>x y. a = Inr x \<and> b = Inr y \<and> x \<le> y)\<close>

lemma less_eq_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<le> Inl y \<longleftrightarrow> x \<le> y\<close>
  \<open>\<And>x y. Inr x \<le> Inr y \<longleftrightarrow> x \<le> y\<close>
  \<open>\<And>x y. Inl x \<le> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<le> Inl y \<longleftrightarrow> False\<close>
  by (simp add: less_eq_sum_def)+

definition less_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool\<close> where
  \<open>less_sum a b \<equiv>
    (\<exists>x y. a = Inl x \<and> b = Inl y \<and> x < y) \<or>
    (\<exists>x y. a = Inr x \<and> b = Inr y \<and> x < y)\<close>

lemma less_sum_simps[simp]:
  \<open>\<And>x y. Inl x < Inl y \<longleftrightarrow> x < y\<close>
  \<open>\<And>x y. Inr x < Inr y \<longleftrightarrow> x < y\<close>
  \<open>\<And>x y. Inl x < Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x < Inl y \<longleftrightarrow> False\<close>
  by (simp add: less_sum_def less_eq_sum_def)+

instance
  apply standard
     apply (case_tac x; case_tac y; simp add: less_le_not_le)
    apply (case_tac x; simp)
   apply (case_tac x; case_tac y; case_tac z; simp)
  apply (case_tac x; case_tac y; simp)
  done

end

subsection \<open> perm_alg \<close>

instantiation sum :: (pre_perm_alg,pre_perm_alg) pre_perm_alg
begin

definition disjoint_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_sum a b \<equiv>
    (\<exists>x y. a = Inl x \<and> b = Inl y \<and> x ## y) \<or>
    (\<exists>x y. a = Inr x \<and> b = Inr y \<and> x ## y)\<close>

lemma disjoint_sum_simps[simp]:
  \<open>\<And>x y. Inl x ## Inl y = x ## y\<close>
  \<open>\<And>x y. Inr x ## Inr y = x ## y\<close>
  \<open>\<And>x y. Inl x ## Inr y = False\<close>
  \<open>\<And>x y. Inr x ## Inl y = False\<close>
  by (simp add: disjoint_sum_def)+

definition plus_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b\<close> where
  \<open>plus_sum a b \<equiv>
      case a of
        Inl x \<Rightarrow>
          (case b of
            Inl y \<Rightarrow> Inl (x + y)
          | Inr y \<Rightarrow> undefined)
      | Inr x \<Rightarrow>
          (case b of
            Inl y \<Rightarrow> undefined
          | Inr y \<Rightarrow> Inr (x + y))\<close>

lemma plus_sum_simps[simp]:
  \<open>\<And>x y. Inl x + Inl y = Inl (x + y)\<close>
  \<open>\<And>x y. Inr x + Inr y = Inr (x + y)\<close>
  by (simp add: plus_sum_def)+

instance
  apply standard
      apply (simp add: disjoint_sum_def)
      apply (elim disjE; force simp add: partial_add_assoc)
     apply (simp add: disjoint_sum_def)
     apply (elim disjE; force dest: partial_add_commute)
    apply (simp add: disjoint_sum_def)
    apply (elim disjE exE conjE; force dest: disjoint_sym)
   apply (simp add: disjoint_sum_def)
   apply (elim disjE exE conjE; force dest: disjoint_add_rightL)
  apply (simp add: disjoint_sum_def)
  apply (elim disjE exE conjE; force dest: disjoint_add_right_commute)
  done

end

instance sum :: (perm_alg, perm_alg) perm_alg
  by standard
    (force simp add: disjoint_sum_def dest: positivity)

lemma part_of_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<lesssim> Inl y \<longleftrightarrow> x \<lesssim> y\<close>
  \<open>\<And>x y. Inr x \<lesssim> Inr y \<longleftrightarrow> x \<lesssim> y\<close>
  \<open>\<And>x y. Inl x \<lesssim> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<lesssim> Inl y \<longleftrightarrow> False\<close>
     apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
     apply (metis Inl_inject obj_sumE sum.distinct(1))
    apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
    apply (metis Inr_inject obj_sumE sum.distinct(1))
   apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
  apply (simp add: part_of_def disjoint_sum_def plus_sum_def split: sum.splits)
  done

lemma less_eq_sepadd_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<preceq> Inl y \<longleftrightarrow> x \<preceq> y\<close>
  \<open>\<And>x y. Inr x \<preceq> Inr y \<longleftrightarrow> x \<preceq> y\<close>
  \<open>\<And>x y. Inl x \<preceq> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<preceq> Inl y \<longleftrightarrow> False\<close>
  apply -
     apply (simp add: less_eq_sepadd_def plus_sum_def split: sum.splits)
     apply (metis sum.distinct(1) sum.inject(1) sumE)
    apply (simp add: less_eq_sepadd_def plus_sum_def split: sum.splits)
    apply (metis Inr_inject obj_sumE sum.distinct(1))
   apply (simp add: less_eq_sepadd_def plus_sum_def split: sum.splits)
  apply (simp add: less_eq_sepadd_def plus_sum_def split: sum.splits)
  done

lemma less_sepadd_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<prec> Inl y \<longleftrightarrow> x \<prec> y\<close>
  \<open>\<And>x y. Inr x \<prec> Inr y \<longleftrightarrow> x \<prec> y\<close>
  \<open>\<And>x y. Inl x \<prec> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<prec> Inl y \<longleftrightarrow> False\<close>
  by (simp add: resource_preorder.less_le_not_le)+


subsection \<open> mu_sep_alg \<close>

instantiation sum :: (multiunit_sep_alg,multiunit_sep_alg) multiunit_sep_alg
begin

definition unitof_sum :: \<open>'a + 'b \<Rightarrow> 'a + 'b\<close> where
  \<open>unitof_sum \<equiv> map_sum unitof unitof\<close>

lemmas unitof_simps[simp] =
  map_sum.simps[
    of \<open>unitof :: 'a \<Rightarrow> _\<close> \<open>unitof :: 'b \<Rightarrow> _\<close>,
    unfolded unitof_sum_def[symmetric]]

instance
  apply standard
   apply (case_tac a; simp)
  apply (case_tac a; case_tac b; simp)
  done

end

subsection \<open> Extended instances \<close>

instance sum :: (dupcl_perm_alg, dupcl_perm_alg) dupcl_perm_alg
  apply standard
  apply (simp add: disjoint_sum_def)
  apply (elim disjE exE conjE; force dest: dup_sub_closure)
  done


section \<open> (multiplicative) unit \<close>

typedef munit = \<open>{()}\<close>
  by blast

abbreviation munit :: munit (\<open>\<one>\<close>) where
  \<open>\<one> \<equiv> Abs_munit ()\<close>

lemma eq_munit_iff[iff]:
  \<open>a = (b::munit)\<close>
  using Rep_munit_inject by auto

instantiation munit :: order
begin

definition less_eq_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> bool\<close> where
  \<open>less_eq_munit a b \<equiv> True\<close>
declare less_eq_munit_def[simp]

definition less_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> bool\<close> where
  \<open>less_munit a b \<equiv> False\<close>
declare less_munit_def[simp]

instance
  by standard simp+

end

instantiation munit :: perm_alg
begin

definition plus_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> munit\<close> where
  \<open>plus_munit a b \<equiv> undefined\<close>
declare plus_munit_def[simp]

definition disjoint_munit :: \<open>munit \<Rightarrow> munit \<Rightarrow> bool\<close> where
  \<open>disjoint_munit a b \<equiv> False\<close>
declare disjoint_munit_def[simp]

instance
  by standard simp+

end

subsection \<open> Extended instances \<close>

instance munit :: dupcl_perm_alg
  by standard simp

(* not a allcompatible_perm_alg *)

instance munit :: strong_sep_pre_perm_alg
  by standard simp

instance munit :: disjoint_parts_pre_perm_alg
  by standard simp

instance munit :: trivial_selfdisjoint_pre_perm_alg
  by standard simp

instance munit :: crosssplit_pre_perm_alg
  by standard simp

instance munit :: cancel_pre_perm_alg
  by standard simp

instance munit :: no_unit_pre_perm_alg
  by standard (simp add: sepadd_unit_def)

(* not a halving_perm_alg *)

(* not an all_disjoint_pre_perm_alg *)


section \<open> option \<close>

instantiation option :: (disjoint) disjoint
begin
definition disjoint_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>disjoint_option a b \<equiv>
    case a of None \<Rightarrow> True | Some x \<Rightarrow>
      (case b of None \<Rightarrow> True | Some y \<Rightarrow> x ## y)\<close>
instance by standard
end

lemma disjoint_option_simps[simp]:
  \<open>Some x ## Some y \<longleftrightarrow> x ## y\<close>
  \<open>None ## b\<close>
  \<open>a ## None\<close>
  by (simp add: disjoint_option_def split: option.splits)+

lemma disjoint_option_iff:
  \<open>Some x ## b \<longleftrightarrow> b = None \<or> (\<exists>y. b = Some y \<and> x ## y)\<close>
  \<open>a ## Some y \<longleftrightarrow> a = None \<or> (\<exists>x. a = Some x \<and> x ## y)\<close>
  by (simp add: disjoint_option_def split: option.splits)+

lemma disjoint_option_def2:
  \<open>a ## b \<longleftrightarrow> a = None \<or> b = None \<or> the a ## the b\<close>
  by (cases a; cases b; simp)


instantiation option :: (plus) plus
begin
definition plus_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> 'a option\<close> where
  \<open>plus_option a b \<equiv>
    case a of None \<Rightarrow> b | Some x \<Rightarrow>
      (case b of None \<Rightarrow> a | Some y \<Rightarrow> Some (x + y))\<close>
instance by standard
end

lemma plus_option_simps[simp]:
  \<open>Some x + Some y = Some (x + y)\<close>
  \<open>None + b = b\<close>
  \<open>a + None = a\<close>
  by (simp add: plus_option_def split: option.splits)+

lemma plus_option_iff:
  \<open>a + b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  \<open>a + b = Some z \<longleftrightarrow>
    (a = None \<and> b = Some z) \<or>
    (\<exists>x. a = Some x \<and> b = None \<and> z = x) \<or>
    (\<exists>x y. a = Some x \<and> b = Some y \<and> z = x + y)\<close>
  by (force simp add: disjoint_option_def plus_option_def split: option.splits)+

lemmas plus_option_iff2 =
  trans[OF eq_commute plus_option_iff(1)]
  trans[OF eq_commute plus_option_iff(2)]


instance option :: (pre_perm_alg) pre_perm_alg
  apply standard
      apply (simp add: disjoint_option_def plus_option_def partial_add_assoc
      split: option.splits; fail)
     apply (simp add: disjoint_option_def plus_option_def split: option.splits,
      metis partial_add_commute; fail)
    apply (metis disjoint_option_def2 disjoint_sym)
   apply (simp add: disjoint_option_def split: option.splits,
      metis disjoint_add_rightL; fail)
  apply (simp add: disjoint_option_def disjoint_sym_iff
      disjoint_add_right_commute split: option.splits; fail)
  done

instance option :: (positivity_law) positivity_law
  by standard
    (simp add: disjoint_option_def positivity split: option.splits; fail)

instance option :: (perm_alg) perm_alg
  by standard

lemma less_eq_sepadd_option_simps[simp]:
  \<open>None \<preceq> a\<close>
  \<open>Some x \<preceq> None \<longleftrightarrow> False\<close>
  \<open>Some x \<preceq> Some y \<longleftrightarrow> x \<preceq> y\<close>
  by (force simp add: less_eq_sepadd_def disjoint_option_iff)+

lemma less_sepadd_option_simps[simp]:
  \<open>a \<prec> None \<longleftrightarrow> False\<close>
  \<open>None \<prec> Some x\<close>
  \<open>Some x \<prec> Some y \<longleftrightarrow> x \<prec> y\<close>
  by (simp add: resource_preordering.strict_iff_not)+

instantiation option :: (pre_perm_alg) pre_multiunit_sep_alg
begin

definition unitof_option :: \<open>'a option \<Rightarrow> 'a option\<close> where
  \<open>unitof_option x \<equiv> None\<close>
declare unitof_option_def[simp]

instance
  by standard force+

end

instance option :: (perm_alg) multiunit_sep_alg
  by standard

instantiation option :: (pre_perm_alg) pre_sep_alg 
begin

definition zero_option :: \<open>'a option\<close> where
  \<open>zero_option \<equiv> None\<close>
declare zero_option_def[simp]

definition bot_option :: \<open>'a option\<close> where
  \<open>bot_option \<equiv> None\<close>
declare bot_option_def[simp]

instance
  by standard force+

end

instance option :: (perm_alg) sep_alg
  by standard

subsection \<open> Extended instances \<close>

instance option :: (dupcl_perm_alg) dupcl_perm_alg
  by standard
    (simp add: disjoint_option_def split: option.splits,
      metis dup_sub_closure)

(* is an allcompatible_perm_alg as it's a sep_alg  *)

(* not a strong_sep_pre_perm_alg *)

instance option :: (disjoint_parts_pre_perm_alg) disjoint_parts_pre_perm_alg
  by standard
    (simp add: disjoint_option_def split: option.splits)

instance option :: (trivial_selfdisjoint_pre_perm_alg) trivial_selfdisjoint_pre_perm_alg
  by standard
    (force dest: selfdisjoint_same simp add: disjoint_option_def plus_option_def
      split: option.splits)

instance option :: (crosssplit_pre_perm_alg) crosssplit_pre_perm_alg
  apply standard
  apply (clarsimp simp add: disjoint_option_def plus_option_def
      split: option.splits)
          apply blast
         apply blast
        apply blast
       apply blast
      apply blast
     apply blast
    apply blast
   apply blast
  apply (frule(2) cross_split)
  apply clarsimp
  apply (rule_tac x=\<open>Some ac\<close> in exI)
  apply (rule_tac x=\<open>Some ad\<close> in exI)
  apply simp
  apply (rule_tac x=\<open>Some bc\<close> in exI)
  apply simp
  apply (rule_tac x=\<open>Some bd\<close> in exI)
  apply simp
  done

text \<open>
  The option-instance is only cancellable when the sub-instance is cancellative *and*
  that instance has no units.
\<close>
instance option :: (\<open>{cancel_pre_perm_alg,no_unit_pre_perm_alg}\<close>) cancel_pre_perm_alg
  by standard
    (simp add: disjoint_option_def plus_option_def split: option.splits;
      metis cancel_right_to_unit no_units)

(* not no_unit_pre_perm_alg *)

instantiation option :: (halfof) halfof
begin
definition \<open>halfof_option \<equiv> map_option halfof\<close>
instance ..
end

instance option :: (halving_pre_perm_alg) halving_pre_perm_alg
  by standard
    (simp add: halfof_option_def disjoint_option_def plus_option_def halfof_additive_split
      halfof_self_disjoint halfof_sepadd_distrib split: option.splits)+

instance option :: (all_disjoint_pre_perm_alg) all_disjoint_pre_perm_alg
  by standard (simp add: disjoint_option_def split: option.splits)+


section \<open> functions \<close>

instantiation "fun" :: (type, disjoint) disjoint
begin
definition disjoint_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> where
  \<open>disjoint_fun f g \<equiv> \<forall>x. f x ## g x\<close>
instance by standard
end

lemma disjoint_funI[intro!]:
  \<open>\<forall>x. f x ## g x \<Longrightarrow> f ## g\<close>
  by (simp add: disjoint_fun_def)

instantiation "fun" :: (type, plus) plus
begin
definition plus_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>plus_fun f g \<equiv> \<lambda>x. f x + g x\<close>
instance by standard
end

lemma plus_fun_apply[simp]:
  \<open>(f + g) x = (f x + g x)\<close>
  by (simp add: plus_fun_def)


instance "fun" :: (type, pre_perm_alg) pre_perm_alg
  apply standard
      apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_assoc)
     apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_commute)
    apply (simp add: disjoint_fun_def, metis disjoint_sym)
   apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_rightL)
  apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_right_commute)
  done

instance "fun" :: (type, positivity_law) positivity_law
  apply standard
  apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis positivity)
  done

instance "fun" :: (type, perm_alg) perm_alg
  by standard

lemma fun_positivity_alt:
  fixes a c1 c2 :: \<open>'a \<Rightarrow> 'b::positivity_law\<close>
  shows \<open>a ## c1 \<Longrightarrow> a + c1 ## c2 \<Longrightarrow> a + c1 + c2 = a \<Longrightarrow> a + c1 = a\<close>
  by (simp add: plus_fun_def disjoint_fun_def fun_eq_iff, metis positivity)

lemma less_sepadd_fun_eq:
  fixes f g :: \<open>'a \<Rightarrow> 'b::perm_alg\<close>
  shows \<open>f \<prec> g \<longleftrightarrow> (\<exists>x. f x \<noteq> g x) \<and> (\<forall>x. f x \<lesssim> g x)\<close>
  by (simp add: part_of_def less_sepadd_def' fun_eq_iff disjoint_fun_def, metis)

lemma less_eq_sepadd_fun_eq:
  fixes f g :: \<open>'a \<Rightarrow> 'b::perm_alg\<close>
  shows \<open>f \<preceq> g \<longleftrightarrow> (\<forall>x. f x = g x) \<or> (\<forall>x. f x \<lesssim> g x)\<close>
  by (simp add: part_of_def less_eq_sepadd_def disjoint_fun_def fun_eq_iff, metis)

lemma fun_all_unit_elems_then_unit:
  \<open>\<forall>x. sepadd_unit (f x) \<Longrightarrow> sepadd_unit f\<close>
  by (simp add: disjoint_fun_def plus_fun_def sepadd_unit_def_strong)

instantiation "fun" :: (type, pre_multiunit_sep_alg) pre_multiunit_sep_alg
begin
definition unitof_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>unitof_fun f \<equiv> \<lambda>x. unitof (f x)\<close>
declare unitof_fun_def[simp]

instance
  by standard
    (simp add: disjoint_fun_def plus_fun_def le_fun_def fun_eq_iff le_iff_sepadd; metis)+
end

instantiation "fun" :: (type, multiunit_sep_alg) multiunit_sep_alg
begin

instance by standard

lemma less_sepadd_fun_eq2:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close>
  shows \<open>f \<prec> g \<longleftrightarrow> (\<exists>x. f x \<prec> g x) \<and> (\<forall>x. f x \<preceq> g x)\<close>
  by (metis le_iff_part_of less_sepadd_fun_eq resource_order.less_le)

lemma less_eq_sepadd_fun_eq2:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close>
  shows \<open>f \<preceq> g \<longleftrightarrow> (\<forall>x. f x \<preceq> g x)\<close>
  by (metis less_sepadd_fun_eq2 less_eq_sepadd_fun_eq resource_order.le_less)

end

instantiation "fun" :: (type, pre_sep_alg) pre_sep_alg
begin

definition zero_fun :: \<open>('a \<Rightarrow> 'b)\<close> where
  \<open>zero_fun \<equiv> \<lambda>x. 0\<close>
declare zero_fun_def[simp]

definition bot_fun :: \<open>('a \<Rightarrow> 'b)\<close> where
  \<open>bot_fun \<equiv> \<lambda>x. 0\<close>
declare bot_fun_def[simp]

instance
  by standard
    (fastforce simp add: fun_eq_iff less_eq_sepadd_fun_eq2)+

end

instance "fun" :: (type, sep_alg) sep_alg
  by standard


subsection \<open> Extended instances \<close>

instance "fun" :: (type, dupcl_perm_alg) dupcl_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff,
      metis dup_sub_closure)

(* not allcompatible_perm_alg *)

instance "fun" :: (type, strong_sep_pre_perm_alg) strong_sep_pre_perm_alg
  by standard
    (clarsimp simp add: disjoint_fun_def plus_fun_def fun_eq_iff selfsep_iff
      fun_all_unit_elems_then_unit)

instance "fun" :: (type, disjoint_parts_pre_perm_alg) disjoint_parts_pre_perm_alg
  by standard (simp add: disjoint_fun_def)

instance "fun" :: (type, trivial_selfdisjoint_pre_perm_alg) trivial_selfdisjoint_pre_perm_alg
  by standard
    (force dest: selfdisjoint_same simp add: disjoint_fun_def plus_fun_def fun_eq_iff)

instance "fun" :: (type, crosssplit_pre_perm_alg) crosssplit_pre_perm_alg
proof standard
  fix a b c d :: \<open>'a \<Rightarrow> 'b\<close>
  assume
    \<open>a ## b\<close>
    \<open>c ## d\<close>
    \<open>a + b = c + d\<close>
  then have assms2:
    \<open>\<forall>x. a x ## b x\<close>
    \<open>\<forall>x. c x ## d x\<close>
    \<open>\<forall>x. a x + b x = c x + d x\<close>
    by (simp add: disjoint_fun_def plus_fun_def fun_eq_iff)+
  then have \<open>\<forall>x. \<exists>acx adx bcx bdx.
      acx ## adx \<and> bcx ## bdx \<and> acx ## bcx \<and> adx ## bdx \<and>
      a x = acx + adx \<and> b x = bcx + bdx \<and>
      c x = acx + bcx \<and> d x = adx + bdx\<close>
    using cross_split[of \<open>a x\<close> \<open>b x\<close> \<open>c x\<close> \<open>d x\<close> for x]
    by metis
  then show
    \<open>\<exists>ac ad bc bd.
        ac ## ad \<and> bc ## bd \<and> ac ## bc \<and> ad ## bd \<and>
        ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>
    by (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis)
qed

instance "fun" :: (type, cancel_pre_perm_alg) cancel_pre_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff)

(* not no_unit_pre_perm_alg *)

instantiation "fun" :: (type, halfof) halfof
begin
definition \<open>halfof_fun (f :: 'a \<Rightarrow> 'b) \<equiv> \<lambda>x. halfof (f x)\<close>
instance ..
end

instance "fun" :: (type, halving_pre_perm_alg) halving_pre_perm_alg
  by standard
    (simp add: halfof_fun_def disjoint_fun_def plus_fun_def fun_eq_iff
      halfof_additive_split halfof_self_disjoint halfof_sepadd_distrib)+

instance "fun" :: (type, all_disjoint_pre_perm_alg) all_disjoint_pre_perm_alg
  by standard (simp add: disjoint_fun_def)+


section \<open> Discrete Algebra \<close>

typedef 'a discr = \<open>UNIV :: 'a set\<close>
  morphisms the_discr Discr
  by blast

setup_lifting type_definition_discr

lemmas Discr_inverse_iff[simp] = Discr_inverse[simplified]
lemmas Discr_inject_iff[simp] = Discr_inject[simplified]

instantiation discr :: (type) perm_alg
begin

definition plus_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> 'a discr\<close> where
  \<open>plus_discr a b \<equiv> a\<close>
declare plus_discr_def[simp]

definition disjoint_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>disjoint_discr a b \<equiv> a = b\<close>
declare disjoint_discr_def[simp]

instance
  by standard (force simp add: the_discr_inject)+

end

lemma less_eq_discr_iff[simp]:
  \<open>Discr x \<preceq> Discr y \<longleftrightarrow> x = y\<close>
  by (simp add: less_eq_sepadd_def)

instantiation discr :: (type) multiunit_sep_alg
begin

definition unitof_discr :: \<open>'a discr \<Rightarrow> 'a discr\<close> where
  \<open>unitof_discr x = x\<close>
declare unitof_discr_def[simp]

instance by standard (force simp add: the_discr_inject)+

end

subsection \<open> Extended instances \<close>

(* not sep_alg *)

instance discr :: (type) dupcl_perm_alg
  by standard force

(* not allcompatible_perm_alg *)

instance discr :: (type) strong_sep_pre_perm_alg
  by standard (simp add: sepadd_unit_def)

instance discr :: (type) disjoint_parts_pre_perm_alg
  by standard force

instance discr :: (type) trivial_selfdisjoint_pre_perm_alg
  by standard force

instance discr :: (type) crosssplit_pre_perm_alg
  by standard force

instance discr :: (type) cancel_pre_perm_alg
  by standard force

(* not no_unit_pre_perm_alg *)

instantiation discr :: (type) halfof
begin
definition \<open>halfof_discr (a :: 'a discr) \<equiv> a\<close>
declare halfof_discr_def[simp]
instance ..
end

instance discr :: (type) halving_pre_perm_alg
  by standard simp+

(* not all_disjoint_pre_perm_alg *)

subsection \<open> lifting instances for discr \<close>

instantiation discr :: (minus) minus
begin
lift_definition minus_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> 'a discr\<close> is \<open>minus\<close> .
instance by standard
end

instantiation discr :: (uminus) uminus
begin
lift_definition uminus_discr :: \<open>'a discr \<Rightarrow> 'a discr\<close> is \<open>uminus\<close> .
instance by standard
end

instantiation discr :: (ord) ord
begin
lift_definition less_eq_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> is \<open>(<)\<close> .
instance by standard
end

instantiation discr :: (sup) sup
begin
lift_definition sup_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> 'a discr\<close> is \<open>sup\<close> .
instance by standard
end

instantiation discr :: (inf) inf
begin
lift_definition inf_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> 'a discr\<close> is \<open>inf\<close> .
instance by standard
end

instantiation discr :: (top) top
begin
lift_definition top_discr :: \<open>'a discr\<close> is \<open>top\<close> .
instance by standard
end

instantiation discr :: (bot) bot
begin
lift_definition bot_discr :: \<open>'a discr\<close> is \<open>bot\<close> .
instance by standard
end

instance discr :: (order) order
  by standard (transfer, force)+

instance discr :: (order_top) order_top
  by standard (transfer, simp)+

instance discr :: (order_bot) order_bot
  by standard (transfer, simp)+

instance discr :: (semilattice_sup) semilattice_sup
  by standard (transfer, simp)+

instance discr :: (semilattice_inf) semilattice_inf
  by standard (transfer, simp)+

instance discr :: (lattice) lattice
  by standard (transfer, simp)+

instance discr :: (bounded_lattice) bounded_lattice
  by standard (transfer, simp)+

instance discr :: (distrib_lattice) distrib_lattice
  by standard (transfer, simp add: sup_inf_distrib1)

instance discr :: (boolean_algebra) boolean_algebra
  by standard (transfer, simp add: diff_eq)+


section \<open> Fractional FPermissions \<close>

typedef(overloaded) ('a::\<open>{linordered_semiring,zero_less_one}\<close>) fperm =
  \<open>{x. (0::'a) < x \<and> x \<le> 1}\<close>
  morphisms fperm_val FPerm
  using zero_less_one by blast

setup_lifting type_definition_fperm

subsection \<open> helper lemmas \<close>

lemmas FPerm_inverse_iff[simp] = FPerm_inverse[simplified]
lemmas FPerm_inject_iff[simp] = FPerm_inject[simplified]
lemmas fperm_val_inject_rev = fperm_val_inject[symmetric]

lemma FPerm_eq_iff:
  \<open>0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> FPerm a = pa \<longleftrightarrow> fperm_val pa = a\<close>
  using fperm_val_inverse by fastforce

lemma eq_FPerm_iff:
  \<open>0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> pa = FPerm a \<longleftrightarrow> fperm_val pa = a\<close>
  by (metis FPerm_inverse_iff fperm_val_inverse)

lemma fperm_val_conditions:
  \<open>0 < fperm_val x\<close>
  \<open>fperm_val x \<le> 1\<close>
  using fperm_val by force+

lemma fperm_val_never_zero[simp]:
  \<open>fperm_val x = 0 \<longleftrightarrow> False\<close>
  by (metis less_irrefl fperm_val_conditions(1))

lemma fperm_val_add_gt0:
  \<open>0 < fperm_val x + fperm_val y\<close>
  by (simp add: add_pos_pos fperm_val_conditions(1))

instantiation fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) order
begin

definition less_eq_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> where
  \<open>less_eq_fperm a b \<equiv> fperm_val a \<le> fperm_val b\<close>

lemma less_eq_fperm_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> FPerm x \<le> FPerm y \<longleftrightarrow> x \<le> y\<close>
  by (simp add: less_eq_fperm_def)

definition less_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> where
  \<open>less_fperm a b \<equiv> fperm_val a < fperm_val b\<close>

lemma less_fperm_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> FPerm x < FPerm y \<longleftrightarrow> x < y\<close>
  by (simp add: less_fperm_def)

instance
  apply standard
     apply (force simp add: less_eq_fperm_def less_fperm_def)+
  apply (fastforce simp add: less_eq_fperm_def fperm_val_inject)
  done

end

subsection \<open> perm_alg \<close>

instantiation fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) one
begin
lift_definition one_fperm :: \<open>'a fperm\<close> is \<open>1\<close> by simp
instance by standard
end

instantiation fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) disjoint
begin
lift_definition disjoint_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a + b \<le> 1\<close> .
lemmas disjoint_fperm_iff = disjoint_fperm.rep_eq
instance ..
end

instantiation fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) plus
begin
lift_definition plus_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> 'a fperm\<close> is \<open>\<lambda>x y. min 1 (x + y)\<close>
  by (force simp add: add_pos_pos min_def)
instance ..
end

lemma plus_fperm_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> FPerm x + FPerm y = FPerm (min 1 (x + y))\<close>
  by (simp add: plus_fperm.abs_eq eq_onp_same_args)

lemma plus_fperm_eq:
  \<open>x + y = FPerm (min 1 (fperm_val x + fperm_val y))\<close>
  by (metis fperm_val_inverse plus_fperm.rep_eq)

instance fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) positivity_law
  by standard (transfer, metis add_le_same_cancel1 min_eq_k_iff nless_le)

instance fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) perm_alg
  apply standard
      apply (force simp add: fperm_val_inject_rev add.assoc disjoint_fperm_def plus_fperm.rep_eq)
     apply (force simp add: fperm_val_inject_rev add.commute disjoint_fperm_def plus_fperm.rep_eq)
    apply (simp add: disjoint_fperm_def add.commute; fail)
   apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.assoc[symmetric])
   apply (metis fperm_val_conditions(1) ge0_plus_le_then_left_le add_pos_pos order_less_imp_le)
  apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.left_commute min.coboundedI2
      min_add_distrib_right; fail)
  done

lemma fperm_one_greatest:
  fixes a :: \<open>'a::linordered_semidom fperm\<close>
  shows \<open>a \<preceq> 1\<close>
  unfolding less_eq_sepadd_def
  by (transfer, clarsimp,
      metis add_le_same_cancel2 less_add_same_cancel1 add_diff_inverse nle_le
      order_less_imp_not_less order_neq_less_conv(2))

subsection \<open> Extended instances \<close>

instance fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) dupcl_perm_alg
  by standard (transfer, force)

instance fperm :: (linordered_semidom) allcompatible_perm_alg
  by standard 
    (simp add: compatible_def,
      metis compatible_def fperm_one_greatest trans_le_ge_is_compatible)

(* not a strong_sep_pre_perm_alg *)

(* not a disjoint_parts_pre_perm_alg *)

(* not a trivial_selfdisjoint_pre_perm_alg *)

(* not a crosssplit_pre_perm_alg *)

instance fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) cancel_pre_perm_alg
  by standard (transfer, force)

instance fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) no_unit_pre_perm_alg
  by standard (clarsimp simp add: sepadd_unit_def, transfer, force)

instantiation fperm :: (linordered_field) halfof
begin
lift_definition halfof_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm\<close> is \<open>\<lambda>x. x / 2\<close> by simp
instance ..
end

instance fperm :: (linordered_field) halving_pre_perm_alg
 by standard (transfer, simp)+

(* not an all_disjoint_pre_perm_alg *)


section \<open> Zero-one interval \<close>

typedef(overloaded) ('a::\<open>{linordered_semiring,zero_less_one}\<close>) zoint =
  \<open>{x. (0::'a) \<le> x \<and> x \<le> 1}\<close>
  morphisms zoint_val ZOInt
  using zero_less_one_class.zero_le_one
  by blast

setup_lifting type_definition_zoint

subsection \<open> helper lemmas \<close>

lemmas ZOInt_inverse_iff[simp] = ZOInt_inverse[simplified]
lemmas ZOInt_inject_iff[simp] = ZOInt_inject[simplified]
lemmas zoint_val_inject_rev = zoint_val_inject[symmetric]

lemma ZOInt_eq_iff:
  \<open>0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> ZOInt a = pa \<longleftrightarrow> zoint_val pa = a\<close>
  using zoint_val_inverse by fastforce

lemma eq_ZOInt_iff:
  \<open>0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> pa = ZOInt a \<longleftrightarrow> zoint_val pa = a\<close>
  by (metis ZOInt_inverse_iff zoint_val_inverse)

lemma zoint_val_conditions:
  \<open>0 \<le> zoint_val x\<close>
  \<open>zoint_val x \<le> 1\<close>
  using zoint_val by force+

lemma zoint_val_add_gt0:
  \<open>0 \<le> zoint_val x + zoint_val y\<close>
  by (simp add: add_pos_pos zoint_val_conditions(1))

instantiation zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) order
begin

definition less_eq_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint \<Rightarrow> bool\<close> where
  \<open>less_eq_zoint a b \<equiv> zoint_val a \<le> zoint_val b\<close>

lemma less_eq_zoint_iff[simp]:
  \<open>0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> ZOInt x \<le> ZOInt y \<longleftrightarrow> x \<le> y\<close>
  by (simp add: less_eq_zoint_def)

definition less_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint \<Rightarrow> bool\<close> where
  \<open>less_zoint a b \<equiv> zoint_val a < zoint_val b\<close>

lemma less_zoint_iff[simp]:
  \<open>0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> ZOInt x < ZOInt y \<longleftrightarrow> x < y\<close>
  by (simp add: less_zoint_def)

instance
  apply standard
     apply (force simp add: less_eq_zoint_def less_zoint_def)+
  apply (fastforce simp add: less_eq_zoint_def zoint_val_inject)
  done

end

subsection \<open> perm_alg \<close>

instantiation zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) zero
begin
lift_definition zero_zoint :: \<open>'a zoint\<close> is \<open>0\<close> by simp
declare zero_zoint.rep_eq[simp]
instance by standard
end

instantiation zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) one
begin
lift_definition one_zoint :: \<open>'a zoint\<close> is \<open>1\<close> by simp
declare one_zoint.rep_eq[simp]
instance by standard
end

instantiation zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) plus
begin
lift_definition plus_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint \<Rightarrow> 'a zoint\<close> is \<open>\<lambda>x y. min 1 (x + y)\<close>
  by (force simp add: add_pos_pos min_def)
instance ..
end

lemma plus_zoint_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> ZOInt x + ZOInt y = ZOInt (min 1 (x + y))\<close>
  by (simp add: plus_zoint.abs_eq eq_onp_same_args)

lemma plus_zoint_eq:
  \<open>x + y = ZOInt (min 1 (zoint_val x + zoint_val y))\<close>
  by (metis zoint_val_inverse plus_zoint.rep_eq)

instantiation zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) disjoint
begin
lift_definition disjoint_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a + b \<le> 1\<close> .
lemmas disjoint_zoint_iff = disjoint_zoint.rep_eq
instance ..
end

instance zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) pre_perm_alg
  apply standard
      apply (transfer, simp add: add.commute add.left_commute; fail)
     apply (transfer, simp add: add.commute; fail)
    apply (transfer, simp add: add.commute; fail)
   apply (transfer, simp, metis add.assoc ge0_plus_le_then_left_le nle_le)
  apply (transfer, simp, metis add_increasing add_le_imp_le_left group_cancel.add2 min.absorb_iff2)
  done

instance zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) positivity_law
  by standard
    (transfer, clarsimp, metis add_le_same_cancel1 le_add_same_cancel1 nle_le)

instantiation zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) multiunit_sep_alg
begin
lift_definition unitof_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint\<close> is \<open>\<lambda>x. 0\<close>
  by force
declare unitof_zoint.rep_eq[simp]
instance
  by standard (transfer, simp)+

lemma unitof_zoint_eq[simp]:
  \<open>unitof (x :: 'a zoint) = 0\<close>
  by (transfer, force)
end

instance zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) sep_alg
  apply standard
   apply (simp add: disjoint_zoint_iff zoint_val_conditions(2); fail)
  apply (simp add: plus_zoint_eq zoint_val_conditions(2) zoint_val_inverse; fail)
  done

lemma zoint_one_greatest:
  fixes a :: \<open>'a::linordered_semidom zoint\<close>
  shows \<open>a \<preceq> 1\<close>
  unfolding less_eq_sepadd_def
  apply (transfer, clarsimp)
  apply (metis add_diff_cancel_left' le_add_diff_inverse2 le_numeral_extra(4)
      linordered_semidom_ge0_le_iff_add)
  done

subsection \<open> Extended instances \<close>

instance zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) dupcl_perm_alg
  by standard
    (transfer, simp add: add_nonneg_eq_0_iff)

instance zoint :: (linordered_semidom) allcompatible_perm_alg
  by standard 
    (simp add: compatible_def,
      metis compatible_def zoint_one_greatest trans_le_ge_is_compatible)

(* not a strong_sep_pre_perm_alg *)

(* not a disjoint_parts_pre_perm_alg *)

(* not a trivial_selfdisjoint_pre_perm_alg *)

(* not a crosssplit_pre_perm_alg *)

instance zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) cancel_pre_perm_alg
  by standard (transfer, force)

(* not a no_unit_pre_perm_alg *)

instantiation zoint :: (linordered_field) halving_pre_perm_alg
begin
lift_definition halfof_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint\<close> is \<open>\<lambda>x. x / 2\<close> by simp
instance  by standard (transfer, simp)+
end

(* not an all_disjoint_pre_perm_alg *)


section \<open> Distributive Lattice Separation Algebra \<close>

text \<open>
  This is a lifting of a distributive lattice (with bot) into a sep-algebra,
  such that + \<equiv> \<squnion>, except that you are only able to add when the sup is disjoint
  (that is, a \<sqinter> b = \<bottom>). (Compare the standard heap instance.)

  This is also a generalisation of Krebber's [Krebbers2014] lockable permission structure.
  (Which, in this formulation, is \<open>bool dlat_sep\<close>.) The value \<bottom> represents locked,
  and all other elements denote unlocked values.
  Locked elements are not compatible with other locked elements.
\<close>

typedef ('a::order) dlat_sep = \<open>UNIV :: 'a set\<close>
  by blast

declare Abs_dlat_sep_inject[simplified, simp]
declare Abs_dlat_sep_inverse[simplified, simp]
declare Rep_dlat_sep_inverse[simplified, simp]

lemmas Rep_dlat_sep_inject2 = Rep_dlat_sep_inject[simplified]

lemma Abs_dlat_sep_helpers:
  \<open>(a = Abs_dlat_sep x) \<longleftrightarrow> x = Rep_dlat_sep a\<close>
  \<open>(Abs_dlat_sep x = a) \<longleftrightarrow> x = Rep_dlat_sep a\<close>
  using Abs_dlat_sep_inverse Rep_dlat_sep_inject2
  by force+

setup_lifting type_definition_dlat_sep

subsection \<open> Order + Lattice liftings \<close>

instantiation dlat_sep :: (order) order
begin
lift_definition less_eq_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> bool\<close> is \<open>(<)\<close> .
instance by standard (transfer, force)+
end

instantiation dlat_sep :: (semilattice_inf) semilattice_inf
begin
lift_definition inf_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> 'a dlat_sep\<close> is \<open>(\<sqinter>)\<close> .
instance by standard (transfer, force)+
end

instantiation dlat_sep :: (semilattice_sup) semilattice_sup
begin
lift_definition sup_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> 'a dlat_sep\<close> is \<open>(\<squnion>)\<close> .
instance by standard (transfer, force)+
end

instantiation dlat_sep :: (order_bot) order_bot
begin
lift_definition bot_dlat_sep :: \<open>'a dlat_sep\<close> is \<open>(\<bottom>)\<close> .
instance by standard (transfer, force)+
end

instantiation dlat_sep :: (order_top) order_top
begin
lift_definition top_dlat_sep :: \<open>'a dlat_sep\<close> is \<open>\<top>\<close> .
instance by standard (transfer, force)+
end

instance dlat_sep :: (distrib_lattice) distrib_lattice
  by standard (transfer, force simp add: sup_inf_distrib1)+

instance dlat_sep :: (distrib_lattice_bot) distrib_lattice_bot
  by standard (transfer, force simp add: sup_inf_distrib1)+

instance dlat_sep :: (bounded_distrib_lattice) bounded_distrib_lattice
  by standard (transfer, force simp add: sup_inf_distrib1)+

instantiation dlat_sep :: (boolean_algebra) boolean_algebra
begin
lift_definition minus_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> 'a dlat_sep\<close> is \<open>minus\<close> .
lift_definition uminus_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep\<close> is \<open>uminus\<close> .
instance by standard (transfer, force simp add: diff_eq)+
end


subsection \<open> Permission/Separation algebra instances \<close>

instantiation dlat_sep :: (distrib_lattice_bot) disjoint
begin
lift_definition disjoint_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a \<sqinter> b = \<bottom>\<close> .
lemma disjoint_dlat_sep_simps[simp]:
  fixes a b :: \<open>'a dlat_sep\<close>
  shows \<open>a ## b \<longleftrightarrow> a \<sqinter> b = \<bottom>\<close>
  by (transfer, force)+
instance ..
end

instantiation dlat_sep :: (distrib_lattice_bot) plus
begin
lift_definition plus_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> 'a dlat_sep\<close> is \<open>(\<squnion>)\<close> .
lemma plus_dlat_sep_eq_iff[simp]:
  \<open>a + b = (\<bottom>::'a dlat_sep) \<longleftrightarrow> a = \<bottom> \<and> b = \<bottom>\<close>
  by (transfer, force)+
instance ..
end

instance dlat_sep :: (distrib_lattice_bot) pre_perm_alg
  apply standard
       apply (transfer, metis sup.assoc)
      apply (transfer, metis sup.commute)
     apply (transfer, metis inf.commute)
    apply (transfer, simp add: inf_sup_distrib1; fail)
   apply (transfer, simp add: inf_sup_aci inf_sup_distrib1; fail)
  done

instance dlat_sep :: (distrib_lattice_bot) positivity_law
  by standard (transfer, metis inf_commute inf_sup_absorb)

lemma part_of_dlat_sep_eq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<lesssim> b \<longleftrightarrow> (\<exists>c. Rep_dlat_sep a \<sqinter> c = \<bottom> \<and> Rep_dlat_sep b = Rep_dlat_sep a \<squnion> c)\<close>
  by (simp add: part_of_def, transfer, force)

lemma less_eq_dlat_sep_eq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<preceq> b \<longleftrightarrow> Rep_dlat_sep a = Rep_dlat_sep b \<or>
                    (\<exists>c. Rep_dlat_sep a \<sqinter> c = \<bottom> \<and> Rep_dlat_sep b = Rep_dlat_sep a \<squnion> c)\<close>
  unfolding less_eq_sepadd_def
  by (transfer, blast)

lemma less_dlat_sep_eq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<prec> b \<longleftrightarrow> Rep_dlat_sep a \<noteq> Rep_dlat_sep b \<and>
                    (\<exists>c. Rep_dlat_sep a \<sqinter> c = \<bottom> \<and> Rep_dlat_sep b = Rep_dlat_sep a \<squnion> c)\<close>
  unfolding less_sepadd_def
  by (transfer, force dest: sup_antisym)

lemma sepadd_bot_least[intro]:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>\<bottom> \<preceq> a\<close>
  unfolding less_eq_sepadd_def
  by (transfer, force)

lemma leq_sepadd_then_leq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<preceq> b \<Longrightarrow> a \<le> b\<close>
  by (metis inf.absorb_iff1 inf_sup_absorb le_disj_eq_absorb less_eq_sepadd_def plus_dlat_sep_def
      sup_dlat_sep_def)

lemma less_sepadd_then_less:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<prec> b \<Longrightarrow> a < b\<close>
  by (simp add: leq_sepadd_then_leq less_sepadd_def order_neq_le_trans
      resource_preorder.less_imp_le)

instantiation dlat_sep :: (distrib_lattice_bot) multiunit_sep_alg
begin
lift_definition unitof_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep\<close> is \<open>\<lambda>_. \<bottom>\<close> .
instance by standard (transfer, force)+
end

instantiation dlat_sep :: (bounded_distrib_lattice) sep_alg
begin
lift_definition zero_dlat_sep :: \<open>'a dlat_sep\<close> is \<open>\<bottom>\<close> .
instance
  apply standard
   apply (metis Rep_dlat_sep_inverse SepAlgInstances.zero_dlat_sep.abs_eq unitof_disjoint
      unitof_dlat_sep.abs_eq)
  apply (simp add: plus_dlat_sep_def zero_dlat_sep_def; fail)
  done
end

instance dlat_sep :: (distrib_lattice_bot) dupcl_perm_alg
  by standard
    (transfer, metis sup_idem)

instance dlat_sep :: (distrib_lattice_bot) cancel_pre_perm_alg
  by standard
    (transfer, metis inf_commute inf_sup_absorb inf_sup_distrib1)

instance dlat_sep :: (distrib_lattice_bot) trivial_selfdisjoint_pre_perm_alg
  by standard
    (transfer, metis inf_commute inf_sup_absorb inf_sup_distrib1)

instance dlat_sep :: (distrib_lattice_bot) disjoint_parts_pre_perm_alg
  by standard
    (transfer, simp add: inf_sup_distrib2)

instance dlat_sep :: (distrib_lattice_bot) strong_sep_pre_perm_alg
  by standard
    (transfer, metis cancel_left_to_unit selfdisjoint_same)


section \<open> Heaps and Permission-heaps \<close>

lemma dom_plus_eq[simp]:
  \<open>dom (ma + mb) = dom ma \<union> dom mb\<close>
  apply (simp add: plus_fun_def plus_option_def dom_def split: option.splits)
  apply (clarsimp simp add: imp_conv_disj simp del: disj_not1)
  apply blast
  done

type_synonym ('i,'v) heap = \<open>'i \<rightharpoonup> ('v discr \<times> munit)\<close>

type_synonym ('i,'v) perm_heap = \<open>'i \<rightharpoonup> ('v discr \<times> rat fperm)\<close>

lemma munit_option_plus_simps[simp]:
  fixes x y :: \<open>'a::pre_perm_alg \<times> munit\<close>
  shows
    \<open>Some x ## my \<Longrightarrow> Some x + my = Some x\<close>
    \<open>mx ## Some y \<Longrightarrow> mx + Some y = Some y\<close>
  by (simp add: disjoint_option_iff)+


section \<open> Results \<close>

text \<open> sepdomeq of two maps (with discrete elements) holds exactly when their domains are equal. \<close>
lemma sepdomeq_fun:
  fixes f g :: \<open>('a,'b) heap\<close>
  shows \<open>sepdomeq f g \<longleftrightarrow> dom f = dom g\<close>
  apply (simp add: sepdomeq_def disjoint_fun_def disjoint_option_def split: option.splits)
  apply (rule iffI)
   apply (frule_tac x=\<open>\<lambda>x. if x \<notin> dom f then Some undefined else None\<close> in spec)
   apply (drule_tac x=\<open>\<lambda>x. if x \<notin> dom g then Some undefined else None\<close> in spec)
   apply (clarsimp simp add: dom_def set_eq_iff not_Some_prod_eq[symmetric]
      simp del: not_Some_prod_eq split: if_splits, metis)
  apply blast
  done


section \<open> Failure State \<close>

datatype fail_st = Running | Failed

lemma all_fail_st_eq:
  \<open>All P \<longleftrightarrow> P Running \<and> P Failed\<close>
  by (metis (full_types) fail_st.exhaust)

lemma ex_fail_st_eq:
  \<open>Ex P \<longleftrightarrow> P Running \<or> P Failed\<close>
  by (metis (full_types) fail_st.exhaust)


subsection \<open> Algebra Instances \<close>

\<comment> \<open>
  This is similar to the distributive lattice separation algebra,
  except that addition is always allowed. This fact makes the algebra non-cancellative.
\<close>

subsubsection \<open> Order \<close>

instantiation fail_st :: ord
begin
definition \<open>less_eq_fail_st a b \<equiv> a = b \<or> b = Failed\<close>
definition \<open>less_fail_st a b \<equiv> a = Running \<and> b = Failed\<close>
instance by standard
end

lemma less_eq_fail_st_iff[simp]:
  \<open>Running \<le> b\<close>
  \<open>a \<le> Failed\<close>
  \<open>Failed \<le> b \<longleftrightarrow> b = Failed\<close>
  \<open>a \<le> Running \<longleftrightarrow> a = Running\<close>
  unfolding less_eq_fail_st_def
  by (cut_tac fail_st.nchotomy; metis (full_types))+

lemma less_fail_st_iff[simp]:
  \<open>Running < b \<longleftrightarrow> b = Failed\<close>
  \<open>a < Failed \<longleftrightarrow> a = Running\<close>
  \<open>Failed < b \<longleftrightarrow> False\<close>
  \<open>a < Running \<longleftrightarrow> False\<close>
  unfolding less_fail_st_def
  by (cut_tac fail_st.nchotomy fail_st.simps; metis (full_types))+

instance fail_st :: order
  apply standard
     apply (case_tac x; case_tac y; simp; fail)
    apply (case_tac x; simp; fail)
   apply (case_tac z; simp; fail)
  apply (case_tac x; case_tac y; simp; fail)
  done


subsubsection \<open> Sup \<close>

instantiation fail_st :: sup
begin
definition \<open>sup_fail_st a b \<equiv> if a = Failed \<or> b = Failed then Failed else Running\<close>
instance by standard
end

lemma sup_fail_st_eq[simp]:
  \<open>a \<squnion> Running = a\<close>
  \<open>Running \<squnion> b = b\<close>
  \<open>a \<squnion> Failed = Failed\<close>
  \<open>Failed \<squnion> b = Failed\<close>
  unfolding sup_fail_st_def
  by (cut_tac fail_st.nchotomy; metis (full_types))+

instance fail_st :: semilattice_sup
  by standard (case_tac x; simp; fail)+


subsubsection \<open> Inf \<close>

instantiation fail_st :: inf
begin
definition \<open>inf_fail_st a b \<equiv> if a = Running \<or> b = Running then Running else Failed\<close>
instance by standard
end

lemma inf_fail_st_eq[simp]:
  \<open>a \<sqinter> Running = Running\<close>
  \<open>Running \<sqinter> b = Running\<close>
  \<open>a \<sqinter> Failed = a\<close>
  \<open>Failed \<sqinter> b = b\<close>
  unfolding inf_fail_st_def
  by (cut_tac fail_st.nchotomy; metis)+

instance fail_st :: semilattice_inf
  by standard (case_tac x; simp; fail)+

subsubsection \<open> Bounds \<close>

instantiation fail_st :: top
begin
definition \<open>top_fail_st \<equiv> Failed\<close>
instance by standard
end

instantiation fail_st :: bot
begin
definition \<open>bot_fail_st \<equiv> Running\<close>
instance by standard
end

instance fail_st :: order_top
  by standard (case_tac a; simp add: top_fail_st_def)

instance fail_st :: order_bot
  by standard (case_tac a; simp add: bot_fail_st_def)


subsubsection \<open> Lattice \<close>

\<comment> \<open> automatically a \<open>lattice\<close> \<close>
\<comment> \<open> automatically a \<open>bounded_lattice\<close> \<close>
instance fail_st :: distrib_lattice
  by standard (case_tac x; simp)

subsubsection \<open> Boolean Algebra \<close>

instantiation fail_st :: uminus
begin
definition \<open>uminus_fail_st a \<equiv> if a = Running then Failed else Running\<close>
instance by standard
end

lemma uminus_fail_st_eq[simp]:
  \<open>- Running = Failed\<close>
  \<open>- Failed = Running\<close>
  unfolding uminus_fail_st_def
  by metis+

instantiation fail_st :: minus
begin
definition \<open>minus_fail_st (a::fail_st) b \<equiv> a \<sqinter> - b\<close>
instance by standard
end

lemma minus_fail_st_eq[simp]:
  \<open>Running - a = Running\<close>
  \<open>Failed - a = - a\<close>
  \<open>a - Running = a\<close>
  \<open>a - Failed = Running\<close>
  unfolding minus_fail_st_def
  by (case_tac a; simp)+

instance fail_st :: boolean_algebra
  by standard
    (case_tac x; simp add: bot_fail_st_def top_fail_st_def)+


paragraph \<open> Separation Logic \<close>

instantiation fail_st :: plus
begin
definition \<open>plus_fail_st \<equiv> (\<squnion>) :: fail_st \<Rightarrow> _ \<Rightarrow> _\<close>
instance by standard
end

instantiation fail_st :: disjoint
begin
definition \<open>disjoint_fail_st (a::fail_st) (b::fail_st) \<equiv> True\<close>
instance by standard
end

lemma fail_st_disjoint_eq[simp]:
  \<open>(a::fail_st) ## (b::fail_st)\<close>
  unfolding disjoint_fail_st_def ..

instance fail_st :: pre_perm_alg
  apply standard
      apply (simp add: plus_fail_st_def, metis sup.assoc)
     apply (simp add: plus_fail_st_def, metis sup.commute)
    apply (simp add: plus_fail_st_def)+
  done

instance fail_st :: perm_alg
  by standard (force simp add: plus_fail_st_def dest: sup_antisym)

instantiation fail_st :: multiunit_sep_alg
begin
definition \<open>unitof_fail_st (_::fail_st) \<equiv> Running\<close>
instance
  by standard (simp add: unitof_fail_st_def plus_fail_st_def)+
end

instantiation fail_st :: zero
begin
definition \<open>zero_fail_st \<equiv> Running\<close>
instance by standard
end

instance fail_st :: sep_alg
  by standard (simp add: zero_fail_st_def plus_fail_st_def)+


section \<open> Never-sep Algebra \<close>

typedef 'a neversep = \<open>UNIV :: 'a set\<close>
  morphisms the_neversep NeverSep
  by blast

setup_lifting type_definition_neversep

lemmas NeverSep_inverse_iff[simp] = NeverSep_inverse[simplified]
lemmas NeverSep_inject_iff[simp] = NeverSep_inject[simplified]

instantiation neversep :: (type) plus
begin
definition \<open>plus_neversep (a::'a neversep) (b :: 'a neversep) \<equiv> undefined::'a neversep\<close>
instance by standard
end

instantiation neversep :: (type) disjoint
begin
definition \<open>disjoint_neversep (a::'a neversep) (b :: 'a neversep) \<equiv> False\<close>
instance by standard
end
declare disjoint_neversep_def[simp]

instance neversep :: (type) pre_perm_alg
  by standard simp+

instance neversep :: (type) positivity_law
  by standard simp+


subsection \<open> Extended instances \<close>

(* not pre_multiunit_sep_alg *)
(* not pre_sep_alg *)

instance neversep :: (type) dupcl_perm_alg
  by standard simp

instance neversep :: (type) strong_sep_pre_perm_alg
  by standard simp

instance neversep :: (type) disjoint_parts_pre_perm_alg
  by standard simp

instance neversep :: (type) trivial_selfdisjoint_pre_perm_alg
  by standard simp

instance neversep :: (type) crosssplit_pre_perm_alg
  by standard simp

instance neversep :: (type) cancel_pre_perm_alg
  by standard simp

(* not halving_pre_perm_alg *)

(* not all_disjoint_pre_perm_alg *)

(* not allcompatible_perm_alg *)

instance neversep :: (type) no_unit_pre_perm_alg
  by standard (simp add: sepadd_unit_def)


subsection \<open> lifting instances for neversep \<close>

instantiation neversep :: (minus) minus
begin
lift_definition minus_neversep :: \<open>'a neversep \<Rightarrow> 'a neversep \<Rightarrow> 'a neversep\<close> is \<open>minus\<close> .
instance by standard
end

instantiation neversep :: (uminus) uminus
begin
lift_definition uminus_neversep :: \<open>'a neversep \<Rightarrow> 'a neversep\<close> is \<open>uminus\<close> .
instance by standard
end

instantiation neversep :: (ord) ord
begin
lift_definition less_eq_neversep :: \<open>'a neversep \<Rightarrow> 'a neversep \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_neversep :: \<open>'a neversep \<Rightarrow> 'a neversep \<Rightarrow> bool\<close> is \<open>(<)\<close> .
instance by standard
end

instantiation neversep :: (sup) sup
begin
lift_definition sup_neversep :: \<open>'a neversep \<Rightarrow> 'a neversep \<Rightarrow> 'a neversep\<close> is \<open>sup\<close> .
instance by standard
end

instantiation neversep :: (inf) inf
begin
lift_definition inf_neversep :: \<open>'a neversep \<Rightarrow> 'a neversep \<Rightarrow> 'a neversep\<close> is \<open>inf\<close> .
instance by standard
end

instantiation neversep :: (top) top
begin
lift_definition top_neversep :: \<open>'a neversep\<close> is \<open>top\<close> .
instance by standard
end

instantiation neversep :: (bot) bot
begin
lift_definition bot_neversep :: \<open>'a neversep\<close> is \<open>bot\<close> .
instance by standard
end

instance neversep :: (order) order
  by standard (transfer, force)+

instance neversep :: (order_top) order_top
  by standard (transfer, simp)+

instance neversep :: (order_bot) order_bot
  by standard (transfer, simp)+

instance neversep :: (semilattice_sup) semilattice_sup
  by standard (transfer, simp)+

instance neversep :: (semilattice_inf) semilattice_inf
  by standard (transfer, simp)+

instance neversep :: (lattice) lattice
  by standard (transfer, simp)+

instance neversep :: (bounded_lattice) bounded_lattice
  by standard (transfer, simp)+

instance neversep :: (distrib_lattice) distrib_lattice
  by standard (transfer, simp add: sup_inf_distrib1)

instance neversep :: (boolean_algebra) boolean_algebra
  by standard (transfer, simp add: diff_eq)+


section \<open> Exclusive \<close>

text \<open> Exclusive ownership of the resource. \<close>
type_synonym 'a excl = \<open>'a neversep option\<close>

lemma excl_disjoint_iff[simp]:
  fixes a b :: \<open>'a excl\<close>
  shows
  \<open>a ## b \<longleftrightarrow>
    a = None \<and> b = None \<or>
    (\<exists>v. a = Some (NeverSep v)) \<and> b = None \<or>
    a = None \<and> (\<exists>v. b = Some (NeverSep v))\<close>
  by (metis disjoint_neversep_def disjoint_option_def2 option.exhaust the_neversep_inverse)


section \<open> Bibliography \<close>

text \<open>
  [Krebbers2014] R Krebbers. Separation Algebras for C Verification in Coq. VSTTE 2014.
                  \<^url>\<open>https://doi.org/10.1007/978-3-319-12154-3 10\<close>
\<close>


end
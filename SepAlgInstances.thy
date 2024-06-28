theory SepAlgInstances
  imports SepLogic HOL.Rat "HOL-Library.Product_Order" "HOL-Library.Product_Plus"
begin


section \<open> Product \<close>

declare plus_prod_def[simp]

declare zero_prod_def[simp]

subsection \<open> perm_alg \<close>

instantiation prod :: (perm_alg,perm_alg) perm_alg
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
  apply (force dest: positivity)
  done

end

lemma less_sepadd_prod_eq:
  \<open>a \<prec> b \<longleftrightarrow> (fst a \<noteq> fst b \<or> snd a \<noteq> snd b) \<and> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: less_sepadd_def part_of_def)

lemma less_eq_sepadd_prod_eq:
  \<open>a \<preceq> b \<longleftrightarrow> fst a = fst b \<and> snd a = snd b \<or> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: less_eq_sepadd_def part_of_def)

lemma part_of_prod_eq:
  \<open>a \<lesssim> b \<longleftrightarrow> fst a \<lesssim> fst b \<and> snd a \<lesssim> snd b\<close>
  by (cases a; cases b; force simp add: part_of_def)

subsection \<open> mu_sep_alg \<close>

instantiation prod :: (multiunit_sep_alg,multiunit_sep_alg) multiunit_sep_alg
begin

lemma less_sepadd_prod_eq2[simp]:
  fixes a :: \<open>'a \<times> 'b\<close>
  shows \<open>a \<prec> b \<longleftrightarrow> (fst a \<prec> fst b \<and> snd a \<preceq> snd b \<or> fst a \<preceq> fst b \<and> snd a \<prec> snd b)\<close>
  by (cases a, cases b, clarsimp simp add: less_sepadd_def' less_eq_sepadd_def',
      metis unitof_disjoint2 unitof_is_unitR2)

lemma less_eq_sepadd_prod_eq2[simp]:
  fixes a :: \<open>'a \<times> 'b\<close>
  shows \<open>a \<preceq> b \<longleftrightarrow> fst a \<preceq> fst b \<and> snd a \<preceq> snd b\<close>
  by (cases a, cases b, clarsimp simp add: less_eq_sepadd_def',
      metis unitof_disjoint2 unitof_is_unitR2)

definition unitof_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>unitof \<equiv> map_prod unitof unitof\<close>
declare unitof_prod_def[simp]

instance
  by standard (simp add: less_eq_sepadd_def)+

end

subsection \<open> sep_alg \<close>

instantiation prod :: (sep_alg,sep_alg) sep_alg
begin

declare bot_prod_def[simp]

instance
  by standard (simp add: fun_eq_iff)+

end

lemma prod_sepadd_unit_iff[simp]:
  \<open>sepadd_unit (a, b) \<longleftrightarrow> sepadd_unit a \<and> sepadd_unit b\<close>
  by (simp add: sepadd_unit_def, force)

subsection \<open> Extended instances \<close>

instance prod :: (dupcl_perm_alg, dupcl_perm_alg) dupcl_perm_alg
  by standard (force dest: dup_sub_closure)

(* not an allcompatible_perm_alg *)

instance prod :: (strong_sep_perm_alg, strong_sep_perm_alg) strong_sep_perm_alg
  by standard (clarsimp simp add: selfsep_iff)

instance prod :: (disjoint_parts_perm_alg, disjoint_parts_perm_alg) disjoint_parts_perm_alg
  by standard simp

instance prod :: (trivial_selfdisjoint_perm_alg, trivial_selfdisjoint_perm_alg) trivial_selfdisjoint_perm_alg
  by standard (clarsimp, meson selfdisjoint_same)

instance prod :: (crosssplit_perm_alg, crosssplit_perm_alg) crosssplit_perm_alg
  apply standard
  apply clarsimp
  apply (rename_tac a x b y c z d w)
  apply (frule(2) cross_split[of \<open>_::'a\<close>])
  apply (frule(2) cross_split[of \<open>_::'b\<close>])
  apply clarsimp
  apply metis
  done

instance prod :: (cancel_perm_alg, cancel_perm_alg) cancel_perm_alg
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
instance prod :: (perm_alg, no_unit_perm_alg) no_unit_perm_alg
  by (standard) (metis no_units prod_eq_decompose(2) prod_sepadd_unit_iff)

(*
instance prod :: (perm_alg, no_unit_perm_alg) no_unit_perm_alg
  by (standard) (metis no_units prod_eq_decompose(1) prod_sepadd_unit_iff)
*)

instantiation prod :: (halving_perm_alg, halving_perm_alg) halving_perm_alg
begin
definition \<open>half_prod \<equiv> \<lambda>(a,b). (half a, half b)\<close>
declare half_prod_def[simp]
instance
  by standard
    (clarsimp simp add: half_additive_split half_self_disjoint half_sepadd_distrib
      split: prod.splits)+
end

instance prod :: (all_disjoint_perm_alg, all_disjoint_perm_alg) all_disjoint_perm_alg
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
  :: \<open>('a::perm_alg \<times> 'b::perm_alg \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<^emph>\<and>\<close> 70) where
  \<open>p \<^emph>\<and> q \<equiv> \<lambda>h. \<exists>a b c. a ## b \<and> h = (a + b, c) \<and> p (a, c) \<and> q (b, c)\<close>

lemma sepconj_conjI:
  \<open>p (a, y) \<Longrightarrow> q (b, y) \<Longrightarrow> a ## b \<Longrightarrow> x = a + b \<Longrightarrow> (p \<^emph>\<and> q) (x, y)\<close>
  by (force simp add: sepconj_conj_def)

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

instance unit :: strong_sep_perm_alg
  by standard simp

instance unit :: disjoint_parts_perm_alg
  by standard simp

instance unit :: trivial_selfdisjoint_perm_alg
  by standard simp

instance unit :: crosssplit_perm_alg
  by standard simp

instance unit :: cancel_perm_alg
  by standard simp

(* not a no_unit_perm_alg *)

instantiation unit :: halving_perm_alg
begin
definition \<open>half_unit \<equiv> \<lambda>_::unit. ()\<close>
declare half_unit_def[simp]
instance by standard simp+
end

instance unit :: all_disjoint_perm_alg
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

instantiation sum :: (perm_alg,perm_alg) perm_alg
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
  apply (simp add: disjoint_sum_def)
  apply (elim disjE exE conjE; force dest: positivity)
  done

end

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
  by (simp add: less_eq_sepadd_def)+

lemma less_sepadd_sum_simps[simp]:
  \<open>\<And>x y. Inl x \<prec> Inl y \<longleftrightarrow> x \<prec> y\<close>
  \<open>\<And>x y. Inr x \<prec> Inr y \<longleftrightarrow> x \<prec> y\<close>
  \<open>\<And>x y. Inl x \<prec> Inr y \<longleftrightarrow> False\<close>
  \<open>\<And>x y. Inr x \<prec> Inl y \<longleftrightarrow> False\<close>
  by (simp add: less_sepadd_def)+

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

instance munit :: strong_sep_perm_alg
  by standard simp

instance munit :: disjoint_parts_perm_alg
  by standard simp

instance munit :: trivial_selfdisjoint_perm_alg
  by standard simp

instance munit :: crosssplit_perm_alg
  by standard simp

instance munit :: cancel_perm_alg
  by standard simp

instance munit :: no_unit_perm_alg
  by standard (simp add: sepadd_unit_def)

(* not a halving_perm_alg *)

(* not an all_disjoint_perm_alg *)


section \<open> option \<close>

instantiation option :: (perm_alg) perm_alg
begin

definition disjoint_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>disjoint_option a b \<equiv>
    case a of None \<Rightarrow> True | Some x \<Rightarrow>
      (case b of None \<Rightarrow> True | Some y \<Rightarrow> x ## y)\<close>

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

definition plus_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> 'a option\<close> where
  \<open>plus_option a b \<equiv>
    case a of None \<Rightarrow> b | Some x \<Rightarrow>
      (case b of None \<Rightarrow> a | Some y \<Rightarrow> Some (x + y))\<close>

lemma plus_option_simps[simp]:
  \<open>Some x + Some y = Some (x + y)\<close>
  \<open>None + b = b\<close>
  \<open>a + None = a\<close>
  by (simp add: plus_option_def split: option.splits)+

lemma plus_option_iff:
  \<open>Some x + b = Some z \<longleftrightarrow> (b = None \<and> x = z \<or> (\<exists>y. b = Some y \<and> z = x + y))\<close>
  \<open>a + Some y = Some z \<longleftrightarrow> (a = None \<and> y = z \<or> (\<exists>x. a = Some x \<and> z = x + y))\<close>
  \<open>a + b = None \<longleftrightarrow> a = None \<and> b = None\<close>
  by (force simp add: disjoint_option_def plus_option_def split: option.splits)+

instance
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
  apply (simp add: disjoint_option_def positivity split: option.splits; fail)
  done

end

lemma less_eq_sepadd_option_simps[simp]:
  \<open>None \<preceq> a\<close>
  \<open>Some x \<preceq> None \<longleftrightarrow> False\<close>
  \<open>Some x \<preceq> Some y \<longleftrightarrow> x \<preceq> y\<close>
  by (force simp add: less_eq_sepadd_def' disjoint_option_iff)+

lemma less_sepadd_option_simps[simp]:
  \<open>a \<prec> None \<longleftrightarrow> False\<close>
  \<open>None \<prec> Some x\<close>
  \<open>Some x \<prec> Some y \<longleftrightarrow> x \<prec> y\<close>
  by (simp add: less_sepadd_def' disjoint_option_iff plus_option_iff; blast?; force)+

instantiation option :: (perm_alg) multiunit_sep_alg
begin

definition unitof_option :: \<open>'a option \<Rightarrow> 'a option\<close> where
  \<open>unitof_option x \<equiv> None\<close>
declare unitof_option_def[simp]

instance
  by standard force+

end

instantiation option :: (perm_alg) sep_alg 
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

subsection \<open> Extended instances \<close>

instance option :: (dupcl_perm_alg) dupcl_perm_alg
  by standard
    (simp add: disjoint_option_def split: option.splits,
      metis dup_sub_closure)

(* is an allcompatible_perm_alg as it's a sep_alg  *)

(* not a strong_sep_perm_alg *)

instance option :: (disjoint_parts_perm_alg) disjoint_parts_perm_alg
  by standard
    (simp add: disjoint_option_def split: option.splits)

instance option :: (trivial_selfdisjoint_perm_alg) trivial_selfdisjoint_perm_alg
  by standard
    (force dest: selfdisjoint_same simp add: disjoint_option_def plus_option_def
      split: option.splits)

instance option :: (crosssplit_perm_alg) crosssplit_perm_alg
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
instance option :: (\<open>{cancel_perm_alg,no_unit_perm_alg}\<close>) cancel_perm_alg
  by standard
    (simp add: disjoint_option_def plus_option_def split: option.splits;
      metis cancel_right_to_unit no_units)

(* not no_unit_perm_alg *)

instantiation option :: (halving_perm_alg) halving_perm_alg
begin
definition \<open>half_option \<equiv> map_option half\<close>
instance
  by standard
    (simp add: half_option_def disjoint_option_def plus_option_def half_additive_split
      half_self_disjoint half_sepadd_distrib split: option.splits)+
end

instance option :: (all_disjoint_perm_alg) all_disjoint_perm_alg
  by standard (simp add: disjoint_option_def split: option.splits)+


section \<open> functions \<close>

instantiation "fun" :: (type, perm_alg) perm_alg
begin

definition disjoint_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> where
  \<open>disjoint_fun f g \<equiv> \<forall>x. f x ## g x\<close>

lemma disjoint_funI[intro!]:
  \<open>\<forall>x. f x ## g x \<Longrightarrow> f ## g\<close>
  by (simp add: disjoint_fun_def)

definition plus_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>plus_fun f g \<equiv> \<lambda>x. f x + g x\<close>

lemma plus_fun_apply[simp]:
  \<open>(f + g) x = (f x + g x)\<close>
  by (simp add: plus_fun_def)

instance
  apply standard
       apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_assoc)
      apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis partial_add_commute)
     apply (simp add: disjoint_fun_def, metis disjoint_sym)
    apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_rightL)
   apply (simp add: disjoint_fun_def plus_fun_def, metis disjoint_add_right_commute)
  apply (simp add: disjoint_fun_def plus_fun_def fun_eq_iff, metis positivity)
  done

lemma less_sepadd_fun_eq:
  fixes f g :: \<open>'a \<Rightarrow> 'b::perm_alg\<close>
  shows \<open>f \<prec> g \<longleftrightarrow> (\<exists>x. f x \<noteq> g x) \<and> (\<forall>x. f x \<lesssim> g x)\<close>
  by (simp add: part_of_def less_sepadd_def' fun_eq_iff disjoint_fun_def,
      metis)

lemma less_eq_sepadd_fun_eq:
  fixes f g :: \<open>'a \<Rightarrow> 'b::perm_alg\<close>
  shows \<open>f \<preceq> g \<longleftrightarrow> (\<forall>x. f x = g x) \<or> (\<forall>x. f x \<lesssim> g x)\<close>
  by (simp add: part_of_def less_eq_sepadd_def' disjoint_fun_def fun_eq_iff,
      metis)

end

lemma fun_all_unit_elems_then_unit:
  \<open>\<forall>x. sepadd_unit (f x) \<Longrightarrow> sepadd_unit f\<close>
  by (simp add: disjoint_fun_def plus_fun_def sepadd_unit_def_strong)

instantiation "fun" :: (type, multiunit_sep_alg) multiunit_sep_alg
begin
 
definition unitof_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>unitof_fun f \<equiv> \<lambda>x. unitof (f x)\<close>
declare unitof_fun_def[simp]

instance
  by standard
    (simp add: disjoint_fun_def plus_fun_def le_fun_def fun_eq_iff le_iff_sepadd; metis)+

lemma less_sepadd_fun_eq2:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close>
  shows \<open>f \<prec> g \<longleftrightarrow> (\<exists>x. f x \<prec> g x) \<and> (\<forall>x. f x \<preceq> g x)\<close>
  by (metis le_iff_part_of less_sepadd_def less_sepadd_fun_eq)

lemma less_eq_sepadd_fun_eq2:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close>
  shows \<open>f \<preceq> g \<longleftrightarrow> (\<forall>x. f x \<preceq> g x)\<close>
  by (metis le_iff_part_of less_eq_sepadd_def' less_eq_sepadd_fun_eq)

end


instantiation "fun" :: (type, sep_alg) sep_alg
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

subsection \<open> Extended instances \<close>

instance "fun" :: (type, dupcl_perm_alg) dupcl_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff,
      metis dup_sub_closure)

(* not allcompatible_perm_alg *)

instance "fun" :: (type, strong_sep_perm_alg) strong_sep_perm_alg
  by standard
    (clarsimp simp add: disjoint_fun_def plus_fun_def fun_eq_iff selfsep_iff
      fun_all_unit_elems_then_unit)

instance "fun" :: (type, disjoint_parts_perm_alg) disjoint_parts_perm_alg
  by standard (simp add: disjoint_fun_def)

instance "fun" :: (type, trivial_selfdisjoint_perm_alg) trivial_selfdisjoint_perm_alg
  by standard
    (force dest: selfdisjoint_same simp add: disjoint_fun_def plus_fun_def fun_eq_iff)

instance "fun" :: (type, crosssplit_perm_alg) crosssplit_perm_alg
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

instance "fun" :: (type, cancel_perm_alg) cancel_perm_alg
  by standard
    (simp add: disjoint_fun_def plus_fun_def fun_eq_iff)

(* not no_unit_perm_alg *)

instantiation "fun" :: (type, halving_perm_alg) halving_perm_alg
begin
definition \<open>half_fun (f :: 'a \<Rightarrow> 'b) \<equiv> \<lambda>x. half (f x)\<close>
instance
  by standard
    (simp add: half_fun_def disjoint_fun_def plus_fun_def fun_eq_iff
      half_additive_split half_self_disjoint half_sepadd_distrib)+
end

instance "fun" :: (type, all_disjoint_perm_alg) all_disjoint_perm_alg
  by standard (simp add: disjoint_fun_def)+


section \<open> Discrete Algebra \<close>

typedef 'a discr = \<open>UNIV :: 'a set\<close>
  morphisms the_discr Discr
  by blast

lemmas Discr_inverse_iff[simp] = Discr_inverse[simplified]
lemmas Discr_inject_iff[simp] = Discr_inject[simplified]

instantiation discr :: (type) order
begin

definition less_eq_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>less_eq_discr a b \<equiv> the_discr a = the_discr b\<close>
declare less_eq_discr_def[simp]

definition less_discr :: \<open>'a discr \<Rightarrow> 'a discr \<Rightarrow> bool\<close> where
  \<open>less_discr a b \<equiv> False\<close>
declare less_discr_def[simp]

instance
  by standard (simp add: the_discr_inject)+

end

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
  by (simp add: less_eq_sepadd_def')

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

instance discr :: (type) strong_sep_perm_alg
  by standard (simp add: sepadd_unit_def)

instance discr :: (type) disjoint_parts_perm_alg
  by standard force

instance discr :: (type) trivial_selfdisjoint_perm_alg
  by standard force

instance discr :: (type) crosssplit_perm_alg
  by standard force

instance discr :: (type) cancel_perm_alg
  by standard force

(* not no_unit_perm_alg *)

instantiation discr :: (type) halving_perm_alg
begin
definition \<open>half_discr (a :: 'a discr) \<equiv> a\<close>
declare half_discr_def[simp]
instance by standard simp+
end

(* not all_disjoint_perm_alg *)


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

instantiation fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) perm_alg
begin

lift_definition disjoint_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a + b \<le> 1\<close> .
lemmas disjoint_fperm_iff = disjoint_fperm.rep_eq

lift_definition plus_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm \<Rightarrow> 'a fperm\<close> is \<open>\<lambda>x y. min 1 (x + y)\<close>
  by (force simp add: add_pos_pos min_def)

lemma plus_fperm_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> FPerm x + FPerm y = FPerm (min 1 (x + y))\<close>
  by (simp add: plus_fperm.abs_eq eq_onp_same_args)

lemma plus_fperm_eq:
  \<open>x + y = FPerm (min 1 (fperm_val x + fperm_val y))\<close>
  by (metis fperm_val_inverse plus_fperm.rep_eq)

instance
  apply standard
       apply (force simp add: fperm_val_inject_rev add.assoc disjoint_fperm_def plus_fperm.rep_eq)
      apply (force simp add: fperm_val_inject_rev add.commute disjoint_fperm_def plus_fperm.rep_eq)
     apply (simp add: disjoint_fperm_def add.commute; fail)
    apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.assoc[symmetric])
    apply (metis fperm_val_conditions(1) ge0_plus_le_then_left_le add_pos_pos order_less_imp_le)
   apply (simp add: disjoint_fperm_def plus_fperm.rep_eq add.left_commute min.coboundedI2
      min_add_distrib_right; fail)
  apply (metis disjoint_fperm_iff plus_fperm.rep_eq fperm_val_conditions(1) less_add_same_cancel1
      min.absorb2 not_less_iff_gr_or_eq)
  done

end

lemma fperm_one_greatest:
  fixes a :: \<open>'a::linordered_semidom fperm\<close>
  shows \<open>a \<preceq> 1\<close>
  unfolding less_eq_sepadd_def'
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

(* not a strong_sep_perm_alg *)

(* not a disjoint_parts_perm_alg *)

(* not a trivial_selfdisjoint_perm_alg *)

(* not a crosssplit_perm_alg *)

instance fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) cancel_perm_alg
  by standard (transfer, force)

instance fperm :: (\<open>{linordered_semiring,zero_less_one}\<close>) no_unit_perm_alg
  by standard (clarsimp simp add: sepadd_unit_def, transfer, force)

instantiation fperm :: (linordered_field) halving_perm_alg
begin
lift_definition half_fperm :: \<open>'a fperm \<Rightarrow> 'a fperm\<close> is \<open>\<lambda>x. x / 2\<close> by simp
instance  by standard (transfer, simp)+
end

(* not an all_disjoint_perm_alg *)


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

instantiation zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) sep_alg
begin

lift_definition disjoint_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a + b \<le> 1\<close> .
lemmas disjoint_zoint_iff = disjoint_zoint.rep_eq

lift_definition plus_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint \<Rightarrow> 'a zoint\<close> is \<open>\<lambda>x y. min 1 (x + y)\<close>
  by (force simp add: add_pos_pos min_def)

lemma plus_zoint_iff[simp]:
  \<open>0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> ZOInt x + ZOInt y = ZOInt (min 1 (x + y))\<close>
  by (simp add: plus_zoint.abs_eq eq_onp_same_args)

lemma plus_zoint_eq:
  \<open>x + y = ZOInt (min 1 (zoint_val x + zoint_val y))\<close>
  by (metis zoint_val_inverse plus_zoint.rep_eq)

lift_definition unitof_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint\<close> is \<open>\<lambda>x. 0\<close>
  by force
declare unitof_zoint.rep_eq[simp]

lemma unitof_zoint_eq[simp]:
  \<open>unitof (x :: 'a zoint) = 0\<close>
  by (transfer, force)

lift_definition bot_zoint :: \<open>'a zoint\<close> is \<open>0\<close>
  by force
declare bot_zoint.rep_eq[simp]

instance
  apply standard
           apply (force simp add: zoint_val_inject_rev add.assoc disjoint_zoint_def plus_zoint.rep_eq)
          apply (force simp add: zoint_val_inject_rev add.commute disjoint_zoint_def plus_zoint.rep_eq)
         apply (simp add: disjoint_zoint_def add.commute; fail)
        apply (simp add: disjoint_zoint_def plus_zoint.rep_eq add.assoc[symmetric])
        apply (meson order.trans le_add_same_cancel1 zoint_val_conditions(1))
       apply (simp add: disjoint_zoint_def plus_zoint.rep_eq add.left_commute
      min.coboundedI2 min_add_distrib_right; fail)
      apply (simp add: disjoint_zoint_def zoint_val_inject_rev
      plus_zoint.rep_eq)
      apply (metis add.comm_neutral add_left_mono verit_la_disequality zoint_val_conditions(1))
     apply (simp add: disjoint_zoint_def zoint_val_conditions; fail)
    apply (simp add: disjoint_zoint_def zoint_val_conditions
      zoint_val_inject_rev plus_zoint.rep_eq; fail)
   apply (simp add: disjoint_zoint_iff zoint_val_conditions(2); fail)
  apply (simp add: plus_zoint_eq zoint_val_conditions(2) zoint_val_inverse; fail)
  done

end


lemma zoint_one_greatest:
  fixes a :: \<open>'a::linordered_semidom zoint\<close>
  shows \<open>a \<preceq> 1\<close>
  unfolding less_eq_sepadd_def'
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

(* not a strong_sep_perm_alg *)

(* not a disjoint_parts_perm_alg *)

(* not a trivial_selfdisjoint_perm_alg *)

(* not a crosssplit_perm_alg *)

instance zoint :: (\<open>{linordered_semiring,zero_less_one}\<close>) cancel_perm_alg
  by standard (transfer, force)

(* not a no_unit_perm_alg *)

instantiation zoint :: (linordered_field) halving_perm_alg
begin
lift_definition half_zoint :: \<open>'a zoint \<Rightarrow> 'a zoint\<close> is \<open>\<lambda>x. x / 2\<close> by simp
instance  by standard (transfer, simp)+
end

(* not an all_disjoint_perm_alg *)


section \<open> Error monad \<close>

text \<open>
  Unfortunately, Error does not, in most cases, form a separation algebra.
  The global non-cancellative nature of the Error value breaks the disjoint-subpart law.

  However, it does form a good instance when there are only trivial subparts.
  (I.e. when every element is disjoint.)
\<close>

datatype 'a error =
  Val (the_val: 'a)
  | Error

instantiation error :: (ord) ord
begin

fun less_eq_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>less_eq_error _ Error = True\<close>
| \<open>less_eq_error Error (Val b) = False\<close>
| \<open>less_eq_error (Val a) (Val b) = (a \<le> b)\<close>

lemma less_eq_error_def:
  \<open>a \<le> b =
    (case b of
      Error \<Rightarrow> True
    | Val b \<Rightarrow>
      (case a of
        Error \<Rightarrow> False
      | Val a \<Rightarrow> a \<le> b))\<close>
  by (cases a; cases b; force)

fun less_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>less_error Error _ = False\<close>
| \<open>less_error (Val a) Error = True\<close>
| \<open>less_error (Val a) (Val b) = (a < b)\<close>

lemma less_error_def:
  \<open>a < b =
    (case a of
      Error \<Rightarrow> False
    | Val a \<Rightarrow>
      (case b of
        Error \<Rightarrow> True
      | Val b \<Rightarrow> a < b))\<close>
  by (cases a; cases b; force)

instance proof qed

end

instantiation error :: (preorder) preorder
begin

instance proof
  fix x y z :: \<open>'a :: preorder error\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    by (simp add: less_eq_error_def less_error_def error.case_eq_if less_le_not_le)
  show \<open>x \<le> x\<close>
    by (simp add: less_eq_error_def error.case_eq_if)
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    by (force dest: order_trans simp add: less_eq_error_def split: error.splits)
qed

end


instantiation error :: (order) order_top
begin

definition \<open>top_error \<equiv> Error\<close>

instance proof
  fix x y z :: \<open>'a :: order error\<close>
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_error_def split: error.splits)
  show \<open>x \<le> top\<close>
    by (simp add: top_error_def)
qed

end

instantiation error :: (order_bot) order_bot
begin

definition \<open>bot_error = Val bot\<close>

instance proof
  fix a :: \<open>'a :: order_bot error\<close>
  show \<open>\<bottom> \<le> a\<close>
    by (simp add: bot_error_def less_eq_error_def error.case_eq_if)
qed

end

instantiation error :: (all_disjoint_perm_alg) perm_alg
begin

definition disjoint_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> bool\<close> where
  \<open>disjoint_error a b \<equiv>
    a = Error \<or> b = Error \<or> (\<exists>x y. a = Val x \<and> b = Val y \<and> x ## y)\<close>

lemma disjoint_error_def2:
  \<open>a ## b \<longleftrightarrow> a = Error \<or> b = Error \<or> the_val a ## the_val b\<close>
  by (simp add: disjoint_error_def, metis error.exhaust)

lemma disjoint_error_simps[simp]:
  \<open>Error ## b\<close>
  \<open>a ## Error\<close>
  \<open>Val x ## Val y \<longleftrightarrow> x ## y\<close>
  by (simp add: disjoint_error_def)+


definition plus_error :: \<open>'a error \<Rightarrow> 'a error \<Rightarrow> 'a error\<close> where
  \<open>a + b \<equiv> case a of Val x \<Rightarrow> (case b of Val y \<Rightarrow> Val (x + y) | Error \<Rightarrow> Error) | Error \<Rightarrow> Error\<close>

lemma plus_error_def2:
  \<open>a + b = (if a = Error \<or> b = Error then Error else Val (the_val a + the_val b))\<close>
  by (simp add: error.case_eq_if plus_error_def)

lemma plus_error_simps[simp]:
  \<open>Error + b = Error\<close>
  \<open>a + Error = Error\<close>
  \<open>Val x + Val y = Val (x + y)\<close>
  by (force simp add: plus_error_def split: error.splits)+


instance
  apply standard
       apply (force simp add: disjoint_error_def plus_error_def partial_add_assoc
      split: error.splits)
      apply (force simp add: disjoint_error_def plus_error_def partial_add_commute
      split: error.splits)
     apply (force simp add: disjoint_error_def plus_error_def disjoint_sym_iff)
    apply (simp add: disjoint_error_def plus_error_def disjoint_add_rightL split: error.splits;
      metis error.exhaust)
   apply (force simp add: disjoint_add_right_commute disjoint_error_def)
  apply (force simp add: disjoint_error_def positivity)
  done

end


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


subsection \<open> Permisson/Separation algebra instances \<close>

instantiation dlat_sep :: (distrib_lattice_bot) perm_alg
begin

lift_definition disjoint_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. a \<sqinter> b = \<bottom>\<close> .

lemma disjoint_dlat_sep_simps[simp]:
  fixes a b :: \<open>'a dlat_sep\<close>
  shows \<open>a ## b \<longleftrightarrow> a \<sqinter> b = \<bottom>\<close>
  by (transfer, force)+

lift_definition plus_dlat_sep :: \<open>'a dlat_sep \<Rightarrow> 'a dlat_sep \<Rightarrow> 'a dlat_sep\<close> is \<open>(\<squnion>)\<close> .

lemma plus_dlat_sep_eq_iff[simp]:
  \<open>a + b = (\<bottom>::'a dlat_sep) \<longleftrightarrow> a = \<bottom> \<and> b = \<bottom>\<close>
  by (transfer, force)+

instance
  apply standard
       apply (transfer, metis sup.assoc)
      apply (transfer, metis sup.commute)
     apply (transfer, metis inf.commute)
    apply (transfer, simp add: inf_sup_distrib1; fail)
   apply (transfer, simp add: inf_sup_aci inf_sup_distrib1; fail)
  apply (transfer, metis inf_commute inf_sup_absorb)
  done

lemma part_of_dlat_sep_eq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<lesssim> b \<longleftrightarrow> (\<exists>c. Rep_dlat_sep a \<sqinter> c = \<bottom> \<and> Rep_dlat_sep b = Rep_dlat_sep a \<squnion> c)\<close>
  by (simp add: part_of_def, transfer, force)

lemma less_eq_dlat_sep_eq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<preceq> b \<longleftrightarrow> Rep_dlat_sep a = Rep_dlat_sep b \<or>
                    (\<exists>c. Rep_dlat_sep a \<sqinter> c = \<bottom> \<and> Rep_dlat_sep b = Rep_dlat_sep a \<squnion> c)\<close>
  by (simp add: less_eq_sepadd_def part_of_dlat_sep_eq Rep_dlat_sep_inject2)

lemma less_dlat_sep_eq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<prec> b \<longleftrightarrow> Rep_dlat_sep a \<noteq> Rep_dlat_sep b \<and>
                    (\<exists>c. Rep_dlat_sep a \<sqinter> c = \<bottom> \<and> Rep_dlat_sep b = Rep_dlat_sep a \<squnion> c)\<close>
  by (simp add: less_sepadd_def part_of_dlat_sep_eq Rep_dlat_sep_inject2)

lemma sepadd_bot_least[intro]:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>\<bottom> \<preceq> a\<close>
  by (simp add: less_eq_dlat_sep_eq, transfer, force)

lemma leq_sepadd_then_leq:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<preceq> b \<Longrightarrow> a \<le> b\<close>
  by (simp add: less_eq_dlat_sep_eq, transfer, force)

lemma less_sepadd_then_less:
  fixes a b :: \<open>('a::distrib_lattice_bot) dlat_sep\<close>
  shows \<open>a \<prec> b \<Longrightarrow> a < b\<close>
  by (simp add: less_dlat_sep_eq inf.strict_order_iff, transfer, force)

end

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

instance dlat_sep :: (distrib_lattice_bot) cancel_perm_alg
  by standard
    (transfer, metis inf_commute inf_sup_absorb inf_sup_distrib1)

instance dlat_sep :: (distrib_lattice_bot) trivial_selfdisjoint_perm_alg
  by standard
    (transfer, metis inf_commute inf_sup_absorb inf_sup_distrib1)

instance dlat_sep :: (distrib_lattice_bot) disjoint_parts_perm_alg
  by standard
    (transfer, simp add: inf_sup_distrib2)

instance dlat_sep :: (distrib_lattice_bot) strong_sep_perm_alg
  by standard
    (transfer, metis cancel_left_to_unit selfdisjoint_same)


section \<open> Heaps and Permission-heaps \<close>

type_synonym ('i,'v) heap = \<open>'i \<rightharpoonup> ('v discr \<times> munit)\<close>

type_synonym ('i,'v) perm_heap = \<open>'i \<rightharpoonup> ('v discr \<times> rat fperm)\<close>

definition points_to
  :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close>
  (infix \<open>\<^bold>\<mapsto>\<close> 90)
  where
  \<open>p \<^bold>\<mapsto> v \<equiv> \<lambda>h. h p = Some v\<close>


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


section \<open> Bibliography \<close>

text \<open>
  [Krebbers2014] R Krebbers. Separation Algebras for C Verification in Coq. VSTTE 2014.
                  \<^url>\<open>https://doi.org/10.1007/978-3-319-12154-3 10\<close>
\<close>


end